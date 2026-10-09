import Mathlib
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Support

/-- **Pro-cyclicity of `I/V` in subgroup form.**  For `V ◁ G` and any subgroup `I`, the quotient
`↥I ⧸ V.subgroupOf I` is canonically the image of `I` in `G ⧸ V`: the first isomorphism result of
Noether applied to the restriction of `QuotientGroup.mk' V` to `I`, whose kernel is `V.subgroupOf I`
and whose range is `NK.LocalTame.quotientImage V I = I.map (QuotientGroup.mk' V)`.  Hence
pro-cyclicity of one quotient is pro-cyclicity of the other (transfer along that iso with
`NK.LocalTame.isProCyclic_congr`).  No hypothesis `V ≤ I` is needed.

This is the form in which the pro-cyclicity clause `IsProCyclic ↥(quotientImage V I)` of
`NK.LocalTame.IsMaxNormalProCyclicInQuotient V I` can be checked, and it is used for every
`J ≥ V` in the maximality clause: the classical computation is `I_κ/V_κ ≅ ∏_{ℓ ≠ p} ℤ_ℓ`,
pro-cyclic by CRT (see `Submission/Work/TameStructureDeep/README.md` §3, item 1).

The construction of the underlying iso — the map `↥I →* ↥(quotientImage V I)` obtained by
restricting `QuotientGroup.mk' V` with `MonoidHom.codRestrict`, its kernel `V.subgroupOf I`, and its
surjectivity — is carried out, there with extra hypotheses `[I.Normal]` and `V ≤ I` that this
statement does not need, in
`Submission/Work/TowerRank/isCyclic_quotient_of_isProCyclic_quotientImage.lean`
(`e1 = (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
(QuotientGroup.quotientKerEquivOfSurjective hmk hsurj)`); that chapter imports no module of this
one, so there is no import cycle in consulting or importing it.

File: `Submission/Work/TameStructureDeep/Support/isProCyclic_quotientImage_iff.lean`,
namespace `NK.TameStructureDeep.Support`, with `import Submission.NK.TameStructureDeep.Defs`
(the convention of the sibling files in that directory). -/
theorem isProCyclic_quotientImage_iff {G : Type*} [Group G] {V I : Subgroup G} [V.Normal] :
    NK.LocalTame.IsProCyclic ↥(NK.LocalTame.quotientImage V I) ↔
      NK.LocalTame.IsProCyclic (↥I ⧸ V.subgroupOf I) := by
  -- the canonical surjection `↥I →* ↥(quotientImage V I)`, the restriction of `mk' V` to `I`
  let hmk : ↥I →* ↥(NK.LocalTame.quotientImage V I) :=
    ((QuotientGroup.mk' V).comp I.subtype).codRestrict (NK.LocalTame.quotientImage V I)
      (fun x => Subgroup.mem_map_of_mem (QuotientGroup.mk' V) x.2)
  have hcoe : ∀ x : ↥I, ((hmk x : ↥(NK.LocalTame.quotientImage V I)) : G ⧸ V)
      = (QuotientGroup.mk' V) (x : G) := fun x => rfl
  -- its kernel is `V.subgroupOf I`
  have hker : hmk.ker = V.subgroupOf I := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h2 : (QuotientGroup.mk' V) (x : G) = 1 := by
        have := congrArg (fun z : ↥(NK.LocalTame.quotientImage V I) => (z : G ⧸ V)) h
        simpa [hcoe x] using this
      exact (QuotientGroup.eq_one_iff (x : G)).mp h2
    · intro h
      refine Subtype.ext ?_
      show ((hmk x : ↥(NK.LocalTame.quotientImage V I)) : G ⧸ V) = 1
      rw [hcoe x]
      exact (QuotientGroup.eq_one_iff (x : G)).mpr h
  -- and it is surjective, by definition of the image
  have hsurj : Function.Surjective hmk := by
    rintro ⟨y, hy⟩
    rw [NK.LocalTame.quotientImage, Subgroup.mem_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  -- first isomorphism theorem: `↥I ⧸ V.subgroupOf I ≃* ↥(quotientImage V I)`
  have e1 : ↥I ⧸ V.subgroupOf I ≃* ↥(NK.LocalTame.quotientImage V I) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective hmk hsurj)
  exact NK.LocalTame.isProCyclic_congr e1.symm

end NK.TameStructureDeep.Support
