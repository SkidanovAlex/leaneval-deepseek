import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

open _root_.LightCondensed
open Opposite

/-- Every covering sieve of the one-point light profinite set `pt = ∗` is the maximal sieve: the
only covering sieve of `∗` for the coherent topology on `LightProfinite` is `⊤`.

Route: `coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily` gives a finite effective epi family
`π : (a : α) → Y a ⟶ ∗` whose arrows lie in the sieve; from
`effectiveEpi_desc_iff_effectiveEpiFamily` (needs `FinitaryPreExtensive LightProfinite`) together
with `LightProfinite.epi_iff_surjective` the map `Sigma.desc π : ∐ Y ⟶ ∗` is surjective, hence
some `Y a` is nonempty (compare `∐ Y` with the explicit `CompHausLike.finiteCoproduct Y = ↧(Σ a, Y a)`
via `(colimit.isColimit _).coconePointUniqueUpToIso (CompHausLike.finiteCoproduct.isColimit Y)`;
`CompHausLike.finiteCoproduct.ι_jointly_surjective` describes its points).  For such an `a` and a
point `y : ↥Y a`, the composite `ptAt y ≫ π a` is `𝟙 ∗` (`∗` is terminal), so `𝟙 ∗` lies in the
sieve, and a sieve containing the identity is `⊤`. -/
theorem cover_pt_eq_top (S : (coherentTopology LightProfinite.{0}).Cover Work.ATOM.pt) :
    S = ⊤ := by
  -- The sieve contains a finite effective epimorphic family into `∗`.
  obtain ⟨α, _hα, Y, π, hπ, hmem⟩ :=
    (coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily (S : Sieve Work.ATOM.pt)).mp S.2
  -- `LightProfinite` is finitary pre-extensive, so the family is effective epi iff its
  -- coproduct description is an epimorphism; in `LightProfinite` epis are surjective.
  have hEff : EffectiveEpi (Sigma.desc π) :=
    (effectiveEpi_desc_iff_effectiveEpiFamily Y π).mpr hπ
  obtain ⟨x, -⟩ := (LightProfinite.effectiveEpi_iff_surjective (Sigma.desc π)).mp hEff
    (PUnit.unit : ↥Work.ATOM.pt)
  -- Compare the abstract coproduct with the explicit finite coproduct `↧(Σ a, Y a)`.
  let e : (∐ Y) ≅ CompHausLike.finiteCoproduct Y :=
    (colimit.isColimit (Discrete.functor Y)).coconePointUniqueUpToIso
      (CompHausLike.finiteCoproduct.isColimit Y)
  obtain ⟨a, y, -⟩ := CompHausLike.finiteCoproduct.ι_jointly_surjective Y (e.hom x)
  -- `∗` is terminal, so `ptAt y ≫ π a = 𝟙 ∗`, and a sieve containing `𝟙 ∗` is everything.
  have hpt : Work.ATOM.ptAt y ≫ π a = 𝟙 Work.ATOM.pt :=
    LightProfinite.isTerminalPUnit.hom_ext _ _
  have hmem1 : (S : Sieve Work.ATOM.pt).arrows (𝟙 Work.ATOM.pt) := by
    have h := (S : Sieve Work.ATOM.pt).downward_closed (hmem a) (Work.ATOM.ptAt y)
    rwa [hpt] at h
  have htop : (S : Sieve Work.ATOM.pt) = ⊤ := by
    rw [eq_top_iff]
    intro Z f _
    simpa using (S : Sieve Work.ATOM.pt).downward_closed hmem1 f
  exact Subtype.ext htop

end Work.ANALYTIC
