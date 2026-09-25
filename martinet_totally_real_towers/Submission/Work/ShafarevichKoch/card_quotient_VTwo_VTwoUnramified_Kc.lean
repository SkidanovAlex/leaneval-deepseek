import Mathlib
import Submission.Work.ShafarevichKoch.VTwo_eq_VTwoUnramified_sup_neg_one_Kc
import Submission.Work.ShafarevichKoch.VTwoUnramified
import Submission.Work.ShafarevichKoch.card_VTwoUnramified_mod_squares_Kc
import Submission.Work.ShafarevichKoch.vTwo_rank_two_corrected

/-!
# `Work.ShafarevichKoch.card_quotient_VTwo_VTwoUnramified_Kc`

**The index of the unramified Kummer radical in Koch's radical for `Kc = ℚ(√-30030)` is two:**

```lean
Nat.card (VTwo Kc ⧸ (VTwoUnramified Kc M).subgroupOf (VTwo Kc)) = 2,
```

i.e. `[V_∅ : V^{unr}] = 2`.  This is the numerical form of the slack of the classical relation
bound: `V_∅/Kc^{×2}` has order `2 ^ (d₂(O_{Kc}^×) + rank₂ Cl(Kc)) = 2 ^ (1 + 5) = 64`, while
`V^{unr}/Kc^{×2}` has order `2 ^ rank₂ Cl(Kc) = 2 ^ 5 = 32`, so the single unit class of `-1`
accounts for the whole difference.

## Proof

`(Kcˣ)² ≤ V^{unr} ≤ V_∅` are subgroups of `Kcˣ`.  Multiplicativity of relative indices
(`Subgroup.relIndex_mul_relIndex`)

  `[(Kcˣ)² : V^{unr}] · [V^{unr} : V_∅] = [(Kcˣ)² : V_∅]`

together with the two cardinality computations
(`card_VTwoUnramified_mod_squares_Kc`, `card_vTwo_mod_squares` for `F = Kc`, combined with
`unitTwoRank_witness_eq_one` and `classGroupTwoRank_Kc`) gives `32 · [V_∅ : V^{unr}] = 64`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower
open Work.QuadraticFields

/-- **The unramified radical has index two in Koch's radical for `Kc`.** -/
theorem card_quotient_VTwo_VTwoUnramified_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2) :
    Nat.card (↥(Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc) ⧸
      (Work.ShafarevichKoch.VTwoUnramified Work.ClassFieldTower.Kc M).subgroupOf
        (Work.ShafarevichKoch.VTwo Work.ClassFieldTower.Kc)) = 2 := by
  set V : Subgroup Kcˣ := VTwo Kc with hVdef
  set H : Subgroup Kcˣ := VTwoUnramified Kc M with hHdef
  set S : Subgroup Kcˣ := squareSubgroup Kcˣ with hSdef
  -- the squares are the image of the squaring endomorphism
  have hSmap : S = Subgroup.map (powMonoidHom (2 : ℕ) : Kcˣ →* Kcˣ) ⊤ := by
    rw [hSdef]
    change Subgroup.closure (Set.range fun y : Kcˣ => y ^ 2) = _
    rw [sqSubgroup_eq_range, MonoidHom.range_eq_map]
  -- `(Kcˣ)² ≤ V^{unr} ≤ V_∅`
  have hSH : S ≤ H := by
    intro x hx
    obtain ⟨y, rfl⟩ := (mem_squareSubgroup_iff).mp hx
    exact sq_mem_VTwoUnramified Kc M y
  have hHV : H ≤ V := VTwoUnramified_le_VTwo Kc M
  -- the two cardinalities, i.e. the two relative indices of the squares
  have hcardV : Nat.card (↥V ⧸ S.subgroupOf V) = 64 := by
    rw [hSmap]
    have h := card_vTwo_mod_squares Kc
    rw [unitTwoRank_witness_eq_one, classGroupTwoRank_Kc] at h
    norm_num at h
    exact h
  have hcardH : Nat.card (↥H ⧸ S.subgroupOf H) = 32 := by
    rw [hSmap]
    exact card_VTwoUnramified_mod_squares_Kc M
  have hrelH : S.relIndex H = 32 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hcardH
  have hrelV : S.relIndex V = 64 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hcardV
  -- multiplicativity of relative indices gives `[V_∅ : V^{unr}] = 2`
  have hrelHV : H.relIndex V = 2 := by
    have h := Subgroup.relIndex_mul_relIndex S H V hSH hHV
    rw [hrelH, hrelV] at h
    omega
  exact hrelHV

end Work.ShafarevichKoch
