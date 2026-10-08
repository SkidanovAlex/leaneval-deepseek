import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.ASM.oddCore_odd

/-!
# CORE3 / A7V18: `E ∩ O(X) ≤ Z(E)` for a quasisimple `E` with `E/Z(E) ≅ A₇`

Deliverable `Work.CORE3.A7V18.InfOddCoreLeCenter`.

Let `X` be a finite group, `E ≤ X` quasisimple in the sense of `Work.GW2.IsQuasisimple`
(`⁅E,E⁆ = E` and `E/Z(E)` simple) with `E/Z(E) ≅ A₇`.  Then

  `E ⊓ Work.GW2.oddCore X ≤ (Subgroup.center ↥E).map E.subtype`,

i.e. every element of `E` lying in the largest normal odd-order subgroup of `X` is central in
`E`.

## Mathematics

`M := E ⊓ O(X)` is normal in `E` (`O(X) ◁ X`, so its intersection with `E` is normal in `E`;
no normality of `E` in `X` is needed).  Let `Z := Z(E)` and let `μ : ↥M → ↥E ⧸ Z` be the
composite of the inclusion `M ↪ E` with the quotient map.  Its range is normal in the simple
group `↥E ⧸ Z`, so it is `⊥` or `⊤`.

* If `μ.range = ⊥`, every element of `M` is central in `E`, which is the goal.
* If `μ.range = ⊤`, then `↥E ⧸ Z` is a quotient of `↥M`, so `|↥E ⧸ Z|` divides `|M|`, which is
  odd because `|M|` divides `|O(X)|` and `O(X)` has odd order (`Work.ASM.oddCore_odd`).  But
  `↥E ⧸ Z ≅ A₇` has order `2520 = 2³·3²·5·7`, which is even.  Contradiction.

The second case is where the hypothesis `E/Z(E) ≅ A₇` enters: it only uses that `|E/Z(E)|` is
not odd.
-/

set_option linter.style.haveILetI false

namespace Work.CORE3.A7V18

open Subgroup

/-- `|A₇| = 2520`. -/
theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

/-- **The main lemma.**  A quasisimple subgroup `E` with `E/Z(E) ≅ A₇` meets the largest normal
odd-order subgroup of the ambient group only in its centre. -/
theorem InfOddCoreLeCenter {X : Type} [Group X] [Finite X] (E : Subgroup X)
    (hEq : Work.GW2.IsQuasisimple E)
    (hA7 : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7))) :
    E ⊓ Work.GW2.oddCore X ≤ (Subgroup.center ↥E).map E.subtype := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxE, hxO⟩ := hx
  have hOn : (Work.GW2.oddCore X).Normal := Work.GW2.oddCore_normal X
  -- `M := E ⊓ O(X)` is normal in `E` (its `subgroupOf E` is)
  have hMK : ((E ⊓ Work.GW2.oddCore X).subgroupOf E).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact hOn.subgroupOf E
  -- the composite `μ : ↥M →* ↥E ⧸ Z(E)`
  let μ : ↥(E ⊓ Work.GW2.oddCore X) →* (↥E ⧸ Subgroup.center ↥E) :=
    (QuotientGroup.mk' (Subgroup.center ↥E)).comp
      (Subgroup.inclusion (inf_le_left : E ⊓ Work.GW2.oddCore X ≤ E))
  have hμran : μ.range =
      ((E ⊓ Work.GW2.oddCore X).subgroupOf E).map (QuotientGroup.mk' (Subgroup.center ↥E)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have hμnorm : μ.range.Normal := by
    rw [hμran]
    exact hMK.map _ (QuotientGroup.mk'_surjective _)
  haveI := hEq.2
  have hxM : x ∈ E ⊓ Work.GW2.oddCore X := Subgroup.mem_inf.mpr ⟨hxE, hxO⟩
  have hcase : μ.range = ⊥ ∨ μ.range = ⊤ := by
    haveI := hμnorm
    exact Subgroup.Normal.eq_bot_or_eq_top μ.range
  rcases hcase with hbot | htop
  · -- `μ.range = ⊥`: every element of `M` is central in `E`
    have hzero : μ ⟨x, hxM⟩ = 1 := by
      have : μ ⟨x, hxM⟩ ∈ (⊥ : Subgroup (↥E ⧸ Subgroup.center ↥E)) := by
        rw [← hbot]
        exact MonoidHom.mem_range.mpr ⟨⟨x, hxM⟩, rfl⟩
      simpa using this
    have hincl :
        (Subgroup.inclusion (inf_le_left : E ⊓ Work.GW2.oddCore X ≤ E)) ⟨x, hxM⟩ =
          ⟨x, hxE⟩ :=
      Subtype.ext rfl
    have hk : (QuotientGroup.mk' (Subgroup.center ↥E)) ⟨x, hxE⟩ = 1 := by
      have h := hzero
      simp only [μ, MonoidHom.comp_apply] at h
      rwa [hincl] at h
    have hmem : ⟨x, hxE⟩ ∈ Subgroup.center ↥E := by
      rw [QuotientGroup.mk'_apply] at hk
      exact (QuotientGroup.eq_one_iff _).mp hk
    exact Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, hmem, rfl⟩
  · -- `μ.range = ⊤`: `↥E ⧸ Z(E)` is a quotient of the odd-order group `↥M`, but has order `2520`
    exfalso
    have hsurj : Function.Surjective μ := MonoidHom.range_eq_top.mp htop
    obtain ⟨e⟩ := hA7
    have hcardQ : Nat.card (↥E ⧸ Subgroup.center ↥E) = 2520 := by
      rw [Nat.card_congr e.toEquiv, card_alt7]
    have hdvd : Nat.card (↥E ⧸ Subgroup.center ↥E)
        ∣ Nat.card ↥(E ⊓ Work.GW2.oddCore X) := by
      have h1 := Subgroup.card_map_dvd (⊤ : Subgroup ↥(E ⊓ Work.GW2.oddCore X)) μ
      rw [Subgroup.map_top_of_surjective μ hsurj, Subgroup.card_top] at h1
      simpa using h1
    have hoddM : Odd (Nat.card ↥(E ⊓ Work.GW2.oddCore X)) :=
      Odd.of_dvd_nat (Work.ASM.oddCore_odd X)
        (Subgroup.card_dvd_of_le (inf_le_right : E ⊓ Work.GW2.oddCore X ≤ Work.GW2.oddCore X))
    have hodd : Odd (2520 : ℕ) := by
      rw [← hcardQ]
      exact Odd.of_dvd_nat hoddM hdvd
    exact absurd hodd (by decide)

end Work.CORE3.A7V18
