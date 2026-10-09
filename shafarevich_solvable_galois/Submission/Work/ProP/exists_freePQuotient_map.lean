import Mathlib
import Submission.Work.ProP.Defs
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

open Work.Shrinking

/-- **Transporting along a surjection of free groups.**  A surjective homomorphism
`ψ : FreeGroup (Fin m) →* FreeGroup (Fin n)` (e.g. the retraction of the shrinking procedure for
`n ≤ m`) induces a surjective homomorphism of the generic kernel quotients at every level `ν`,
compatible with the projections.

This is the finite-quotient form of the step in which Schmidt–Wingberg transport a solution at
level `m ≥ n` back to level `n` along a surjective `G`-operator homomorphism `F^(m) → F^(n)`.

Proof: by the compatibility of the filtration with surjections
(`Work.Shrinking.map_pCentralSeries_surjective`),
`(pCentralSeries p (FreeGroup (Fin m)) ν).map ψ = pCentralSeries p (FreeGroup (Fin n)) ν`, so
`QuotientGroup.map` applies to this pair of normal subgroups and gives the required
`f : FreePQuotient p m ν →* FreePQuotient p n ν`; its class-level computation is
`QuotientGroup.map_mk'` (giving the stated compatibility with `freePQuotientMk`), and its
surjectivity follows from that of `ψ` and of the two projections
(`QuotientGroup.map_surjective_of_surjective`, `freePQuotientMk_surjective`). -/
theorem exists_freePQuotient_map {p m n ν : ℕ} (ψ : FreeGroup (Fin m) →* FreeGroup (Fin n))
    (hψ : Function.Surjective ψ) :
    ∃ f : FreePQuotient p m ν →* FreePQuotient p n ν,
      Function.Surjective f ∧
        f.comp (freePQuotientMk p m ν) = (freePQuotientMk p n ν).comp ψ := by
  -- The filtration is compatible with the surjection `ψ`.
  have hmap : (pCentralSeries p (FreeGroup (Fin m)) ν).map ψ
      = pCentralSeries p (FreeGroup (Fin n)) ν :=
    map_pCentralSeries_surjective p ψ hψ ν
  -- Hence `F^(m)(ν) ≤ F^(n)(ν).comap ψ`, which is what `QuotientGroup.map` needs.
  have hle : pCentralSeries p (FreeGroup (Fin m)) ν
      ≤ (pCentralSeries p (FreeGroup (Fin n)) ν).comap ψ := by
    rw [← Subgroup.map_le_iff_le_comap, hmap]
  refine ⟨QuotientGroup.map _ _ ψ hle, ?_, ?_⟩
  · -- Surjectivity: the class of `a` maps to the class of `ψ a`, and `ψ` is onto.
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (pCentralSeries p (FreeGroup (Fin n)) ν) y
    obtain ⟨a, rfl⟩ := hψ b
    exact ⟨QuotientGroup.mk' (pCentralSeries p (FreeGroup (Fin m)) ν) a,
      QuotientGroup.map_mk' _ _ ψ hle a⟩
  · -- Compatibility with the projections is the class-level computation `map_mk'`.
    refine MonoidHom.ext fun x => ?_
    exact QuotientGroup.map_mk' _ _ ψ hle x

end Work.ProP
