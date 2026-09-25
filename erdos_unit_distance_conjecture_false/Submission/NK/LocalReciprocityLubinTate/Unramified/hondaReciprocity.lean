import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.higherUnits_le_normGroup_LTLevel
import Submission.NK.LocalReciprocityLubinTate.Unramified.mem_normGroup_LTLevel_uniformizer
import Submission.NK.LocalReciprocityLubinTate.Unramified.Basic

/-!
# Honda's explicit reciprocity law, proved

For a nonarchimedean local field `F` of characteristic zero, a uniformiser `π` and `n ≥ 1`, the
norm group of the `n`-th Lubin–Tate level `K_n = F(Λ_n)` is

`N_{K_n/F} K_nˣ = ⟨π⟩ · U^n`,   `U^n = 1 + 𝔪[F]^n`

(Serre, *Local Fields*, Ch. XV §5.2; Neukirch, *Algebraic Number Theory*, V.5.5).  This was the
chapter's named classical residue `NK.LocalReciprocityLubinTate.HondaReciprocity`; it is now a
**theorem**, assembled from three proved pieces:

* `NK.LocalReciprocityLubinTate.Unramified.normGroup_LTLevel_le_higherUnits_sup` — the `⊆` half,
  proved by the Coleman norm-operator/resultant computation (`NormOp.lean`, `LTGain.lean`,
  `resultant_LTpolyEis_heart.lean`): a unit of `K_n` has norm `≡ 1 mod π^n`;
* `NK.LocalReciprocityLubinTate.Unramified.mem_normGroup_LTLevel_uniformizer` — `π` itself is a
  norm (the Eisenstein norm computation `Nm(π_n) = ±π`);
* `NK.LocalReciprocityLubinTate.Unramified.higherUnits_le_normGroup_LTLevel` — `U^n` is contained
  in the norm group, obtained from the two index computations
  `index_normGroup_LTLevel` / `index_zpowers_sup_higherUnits` (both `(q-1)q^{n-1}`, the former from
  the norm index theorem for a general local field, `normIndex_of_localField`) by an index squeeze.

## Main result

* `NK.LocalReciprocityLubinTate.Unramified.hondaReciprocity`.
-/

universe u

namespace NK.LocalReciprocityLubinTate.Unramified

/-- **Honda's explicit reciprocity law.**  For every `n ≥ 1`,
`N_{F(Λ_n)/F} F(Λ_n)ˣ = ⟨π⟩ · U^n`, where `U^n = 1 + 𝔪[F]^n` is the `n`-th higher unit group. -/
theorem hondaReciprocity (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] (πu : Fˣ)
    (hπ : NK.LocalReciprocityLubinTate.IsUniformizer F (πu : F)) :
    NK.LocalReciprocityLubinTate.HondaReciprocity F πu
      (NK.LocalReciprocityLubinTate.higherUnits F)
      (NK.LocalReciprocityLubinTate.residueCard F) := by
  intro n hn
  refine le_antisymm
    (normGroup_LTLevel_le_higherUnits_sup F πu hπ n hn) ?_
  refine sup_le ?_ (higherUnits_le_normGroup_LTLevel F πu hπ n hn)
  exact Subgroup.zpowers_le.mpr
    (mem_normGroup_LTLevel_uniformizer F πu hπ n hn)

end NK.LocalReciprocityLubinTate.Unramified
