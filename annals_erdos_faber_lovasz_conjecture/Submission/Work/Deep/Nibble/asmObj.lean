import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs

/-!
# The object vocabulary of the §7 assembly step

Basic lemmas about `objFam` (`objFam N` is a matching of `𝓜` when `N` is an
object matching, distinct colours' object matchings are edge-disjoint after
projection, and the enumeration of a block of colours does not change
cardinalities).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

theorem objFam_subset_edgeSet {𝓜 : MultiHypergraph n} (N : Set (EdgeObj 𝓜)) :
    objFam N ⊆ 𝓜.edgeSet := by
  rintro e ⟨x, -, rfl⟩
  exact EdgeObj.toSet_mem_edgeSet x

theorem isObjMatching_pairwise {𝓜 : MultiHypergraph n} {N : Set (EdgeObj 𝓜)}
    (h : IsObjMatching N) : (objFam N).Pairwise fun e₁ e₂ => Disjoint e₁ e₂ := by
  intro e he e' he' hne
  obtain ⟨x, hx, rfl⟩ := he
  obtain ⟨y, hy, rfl⟩ := he'
  refine h x hx y hy fun hxy => hne ?_
  rw [hxy]

theorem isMatching_objFam {𝓜 : MultiHypergraph n} {N : Set (EdgeObj 𝓜)}
    (h : IsObjMatching N) : MultiHypergraph.IsMatching 𝓜 (objFam N) :=
  ⟨objFam_subset_edgeSet N, isObjMatching_pairwise h⟩

theorem EdgeObj.eq_of_toSet_eq {𝓜 : MultiHypergraph n} {x y : EdgeObj 𝓜}
    (h : EdgeObj.toSet x = EdgeObj.toSet y) (hx : 2 ≤ (EdgeObj.toSet x).ncard) : x = y := by
  have key : ∀ z : EdgeObj 𝓜, 2 ≤ (EdgeObj.toSet z).ncard →
      ∃ a : {e : Set (Fin n) // e ∈ 𝓜.edges}, z = (Sum.inl a : EdgeObj 𝓜) := by
    intro z hz
    cases z with
    | inl a => exact ⟨a, rfl⟩
    | inr p =>
      exfalso
      have h1 : EdgeObj.toSet (Sum.inr p : EdgeObj 𝓜) = ({p.1.1} : Set (Fin n)) :=
        EdgeObj.toSet_inr p
      rw [h1, Set.ncard_singleton] at hz
      omega
  obtain ⟨a, rfl⟩ := key x hx
  obtain ⟨b, hb⟩ := key y (by rw [← h]; exact hx)
  subst hb
  congr 1
  exact Subtype.ext (by rw [← EdgeObj.toSet_inl a, ← EdgeObj.toSet_inl b]; exact h)

theorem edgeDisjointFam_objFam {ι : Type*} {𝓜 : MultiHypergraph n}
    {N : ι → Set (EdgeObj 𝓜)} (h : ∀ i j, i ≠ j → Disjoint (N i) (N j))
    {i j : ι} (hij : i ≠ j) : EdgeDisjointFam (objFam (N i)) (objFam (N j)) := by
  rw [EdgeDisjointFam, Set.disjoint_left]
  rintro e he he'
  obtain ⟨x, hx, hxe⟩ := he.1
  obtain ⟨y, hy, hye⟩ := he'.1
  have hxy : x = y := EdgeObj.eq_of_toSet_eq (by rw [hxe, hye]) (by rw [hxe]; exact he.2)
  exact (Set.disjoint_left.mp (h i j hij) hx) (hxy ▸ hy)

theorem ncard_colour_image {D K : ℕ} {I : Fin K → Finset (Fin D)} (k : Fin K)
    (P : Fin D → Prop) :
    ({i : Fin (I k).card | P (blockColour I k i)} : Set (Fin (I k).card)).ncard =
      ({c : Fin D | c ∈ I k ∧ P c} : Set (Fin D)).ncard := by
  classical
  have himg : blockColour I k '' ({i : Fin (I k).card | P (blockColour I k i)} :
      Set (Fin (I k).card)) = ({c : Fin D | c ∈ I k ∧ P c} : Set (Fin D)) := by
    ext c
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨blockColour_mem I k i, hi⟩
    · rintro ⟨hc, hP⟩
      obtain ⟨i, hi⟩ := exists_blockColour hc
      exact ⟨i, by simpa [hi] using hP, hi⟩
  rw [← himg, Set.ncard_image_of_injective _ (blockColour_injective I k)]

end

end Work.Deep.Nibble
