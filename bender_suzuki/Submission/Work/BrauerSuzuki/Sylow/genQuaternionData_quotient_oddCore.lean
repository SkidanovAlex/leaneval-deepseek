import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Generalized quaternion data passes to `G / O(G)`, with the index `n` preserved

If `S` is a Sylow `2`-subgroup of a finite group `G`, the restriction to `S` of the quotient
map `G → G ⧸ O(G)` is injective (because `S ⊓ O(G) = 1`, the latter having odd order) and its
image is a Sylow `2`-subgroup `T` of the quotient.  Hence `↥S ≃* ↥T`, so the whole generalized
quaternion presentation of `↥S` — *including the parameter `n`* — is carried over to `↥T`.

This is the refinement of `genQuaternion_sylow_quotient` needed by the `Q₈` case (`n = 2`):
the subgroup `T` produced there really is isomorphic to `S`, so a group with `Q₈` Sylow
`2`-subgroups again has `Q₈` Sylow `2`-subgroups after quotenting by `O(G)`.
-/

set_option autoImplicit false

namespace Work.BrauerSuzuki.Sylow

open Submission.Blueprint

/-- The Sylow `2`-subgroup `S` of `G` maps isomorphically onto a Sylow `2`-subgroup of
`G ⧸ O(G)`: the restriction of the quotient map to `S` is injective because `S ⊓ O(G) = 1`,
and its image `S · O(G) / O(G)` is a Sylow `2`-subgroup of the quotient. -/
theorem exists_sylow_quotient_mulEquiv {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    ∃ T : Sylow 2 (G ⧸ Submission.Blueprint.oddCore G), Nonempty (↥S ≃* ↥T) := by
  let O : Subgroup G := Submission.Blueprint.oddCore G
  let π : G →* G ⧸ O := QuotientGroup.mk' O
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  let T : Sylow 2 (G ⧸ O) := Sylow.mapSurjective (p := 2) (f := π) hsurj S
  have hT : (T : Subgroup (G ⧸ O)) = (S : Subgroup G).map π :=
    Sylow.coe_mapSurjective hsurj S
  let f : ↥S →* G ⧸ O := π.comp (S : Subgroup G).subtype
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hx' : π (x : G) = 1 := hx
      have hxO : (x : G) ∈ O := by
        have hker : (x : G) ∈ π.ker := hx'
        rwa [show π.ker = O from QuotientGroup.ker_mk' O] at hker
      have hmem : (x : G) ∈ (S : Subgroup G) ⊓ O := ⟨x.2, hxO⟩
      rw [inf_oddCore_eq_bot S, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    · intro hx
      rw [hx]
      rfl
  have hrange : f.range = (S : Subgroup G).map π := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  exact ⟨T, ⟨(MonoidHom.ofInjective hinj).trans
    (MulEquiv.subgroupCongr (hrange.trans hT.symm))⟩⟩

theorem genQuaternionData_quotient_oddCore {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) :
    ∃ (T : Sylow 2 (G ⧸ Submission.Blueprint.oddCore G))
      (d' : Work.BrauerSuzuki.GenQuaternionData ↥T), d'.n = 2 := by
  obtain ⟨T, ⟨e⟩⟩ := exists_sylow_quotient_mulEquiv S
  have hgen : Work.BrauerSuzuki.IsGenQuaternion ↥T :=
    isGenQuaternion_of_mulEquiv e ⟨d⟩
  obtain ⟨d'⟩ := hgen
  refine ⟨T, d', ?_⟩
  have hcardT : Nat.card ↥T = 2 ^ (d'.n + 1) :=
    (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d').1
  have hcardS : Nat.card ↥S = 2 ^ (d.n + 1) :=
    (Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d).1
  have hcards : Nat.card ↥S = Nat.card ↥T := Nat.card_congr e.toEquiv
  have hpow : 2 ^ (d'.n + 1) = 2 ^ (d.n + 1) := by rw [← hcardT, ← hcards, hcardS]
  have hnn : d'.n + 1 = d.n + 1 := Nat.pow_right_injective (a := 2) (by norm_num) hpow
  omega

end Work.BrauerSuzuki.Sylow
