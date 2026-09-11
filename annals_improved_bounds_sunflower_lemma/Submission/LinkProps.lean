import Mathlib
import Submission.SunBasic
import Submission.SunExtras
import Submission.SunLift

/-!
# The link family `F_T = {A \ T : A ∈ F, T ⊆ A}`
-/
open Finset

namespace Submission.Sun

variable {α : Type*} [DecidableEq α]

/-- the link family at T -/
def link (F : Finset (Finset α)) (T : Finset α) : Finset (Finset α) :=
  (F.filter (fun A : Finset α => T ⊆ A)).image (fun A : Finset α => A \ T)

/-- membership -/
lemma mem_link {F : Finset (Finset α)} {T B : Finset α} :
    B ∈ link F T ↔ ∃ A ∈ F, T ⊆ A ∧ B = A \ T := by
  unfold link
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨A, hA, hBA⟩
    rcases Finset.mem_filter.mp hA with ⟨hAF, hTA⟩
    exact ⟨A, hAF, hTA, hBA.symm⟩
  · rintro ⟨A, hAF, hTA, hBA⟩
    rw [hBA]
    exact Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hTA⟩, rfl⟩

/-- members are disjoint from T -/
lemma link_mem_disjoint {F : Finset (Finset α)} {T B : Finset α} (hB : B ∈ link F T) :
    Disjoint B T := by
  rcases (mem_link.mp hB) with ⟨A, hAF, hTA, hBA⟩
  subst B
  exact (Finset.disjoint_sdiff (s := T) (t := A)).symm

/-- sizes: members are (k-|T|)-uniform -/
lemma link_mem_card {F : Finset (Finset α)} {T B : Finset α} {k : ℕ}
    (hB : B ∈ link F T) (huni : ∀ A ∈ F, A.card = k) (_hTsub : ∀ A ∈ F, T ⊆ A → k - T.card ≤ (A \ T).card) :
    B.card = k - T.card := by
  rcases (mem_link.mp hB) with ⟨A, hAF, hTA, hBA⟩
  subst B
  have hinter : T ∩ A = T := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      exact (Finset.mem_inter.mp hx).1
    · intro hx
      exact Finset.mem_inter.mpr ⟨hx, hTA hx⟩
  rw [Finset.card_sdiff, huni A hAF, hinter]

/-- the link has the same cardinality as the filter (A ↦ A\T injective on {A ⊇ T}) -/
lemma link_card {F : Finset (Finset α)} {T : Finset α} :
    (link F T).card = (F.filter (fun A : Finset α => T ⊆ A)).card := by
  unfold link
  apply Finset.card_image_of_injOn
  intro A hA B hB hEq
  rw [Finset.mem_coe] at hA hB
  have hTA : T ⊆ A := (Finset.mem_filter.mp hA).2
  have hTB : T ⊆ B := (Finset.mem_filter.mp hB).2
  change A \ T = B \ T at hEq
  calc
    A = (A \ T) ∪ T := (Finset.sdiff_union_of_subset hTA).symm
    _ = (B \ T) ∪ T := by rw [hEq]
    _ = B := Finset.sdiff_union_of_subset hTB

/-- a sunflower-free family has sunflower-free links -/
lemma link_sunflower_free {F : Finset (Finset α)} {T : Finset α} {p : ℕ}
    (hfree : SunflowerFree F p) : SunflowerFree (link F T) p := by
  intro hlink
  rcases hlink with ⟨S, hSsub, hSsf⟩
  have hT : ∀ B ∈ S, Disjoint B T := by
    intro B hB
    exact link_mem_disjoint (hSsub hB)
  have hlift : IsSunflower (S.image (fun B : Finset α => T ∪ B)) p := by
    exact IsSunflower_lift_disj T hT hSsf
  have hsubF : S.image (fun B : Finset α => T ∪ B) ⊆ F := by
    rw [Finset.image_subset_iff]
    intro B hB
    rcases (mem_link.mp (hSsub hB)) with ⟨A, hAF, hTA, hBA⟩
    rw [hBA, Finset.union_sdiff_of_subset hTA]
    exact hAF
  exact hfree ⟨S.image (fun B : Finset α => T ∪ B), hsubF, hlift⟩

end Submission.Sun
