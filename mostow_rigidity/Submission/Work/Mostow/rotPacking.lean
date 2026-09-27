import Mathlib
import Submission.Work.Mostow.bieberbachDefs

/-!
# Packing of rotations with a uniform gap (`rotPacking`)

For every `m` and every `θ > 0` there is a bound `N` such that any family of linear isometries of
`ℝ^m` which is `θ`-separated in operator norm,

`θ ≤ ‖opOf A − opOf B‖` for distinct `A, B` in the family,

is finite of cardinality at most `N`.

This is the elementary compactness fact that the orthogonal group `O(m)` is totally bounded in
operator norm: a fixed finite `θ/2`-net (`exists_cover_rotations`, from the Bieberbach chapter)
meets every ball of radius `θ/2` — and balls of radius `θ/2` contain at most one point of a
`θ`-separated set.  So the family injects into the finite net.

This is the counting input behind the *elliptic gap* used in the proof of Mostow rigidity: the
order of any finite (in particular any elliptic) subgroup of a discrete group of isometries of
`ℍⁿ` is bounded in terms of the dimension alone.
-/

namespace Work.Mostow

open Submission.Mostow

set_option linter.style.haveILetI false

/-- **Packing of rotations with a uniform gap.**  For every `θ > 0` there is `N`, depending only
on `m` and `θ`, such that a `θ`-separated (in operator norm `‖opOf · − opOf ·‖`) set of linear
isometries of `ℝ^m` is finite of cardinality at most `N`. -/
theorem rotPacking (m : ℕ) : ∀ θ : ℝ, 0 < θ →
    ∃ N : ℕ, ∀ S : Set (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m),
      (∀ A ∈ S, ∀ B ∈ S, A ≠ B → θ ≤ ‖Work.Mostow.opOf A - Work.Mostow.opOf B‖) →
      S.Finite ∧ S.ncard ≤ N := by
  intro θ hθ
  -- A fixed finite `θ/2`-net of the orthogonal group.
  obtain ⟨F, hF⟩ := exists_cover_rotations (m := m) (θ/2) (by linarith)
  refine ⟨F.card, fun S hS => ?_⟩
  classical
  -- Send each element of `S` to a net point within `θ/2` of it.
  let g : ↥S → ↥F := fun A =>
    ⟨Classical.choose (hF A.1), (Classical.choose_spec (hF A.1)).1⟩
  have hg : ∀ A : ↥S, ‖opOf A.1 - (g A : E m →L[ℝ] E m)‖ < θ/2 := fun A =>
    (Classical.choose_spec (hF A.1)).2
  -- `g` is injective: two elements in one ball of radius `θ/2` are closer than `θ`.
  have hinj : Function.Injective g := by
    intro A B hAB
    by_contra hne
    have hAne : A.1 ≠ B.1 := fun h => hne (Subtype.ext h)
    have hval : (g A : E m →L[ℝ] E m) = (g B : E m →L[ℝ] E m) := by rw [hAB]
    have hclose : ‖opOf A.1 - opOf B.1‖ < θ := by
      have h1 : ‖opOf A.1 - (g A : E m →L[ℝ] E m)‖ < θ/2 := hg A
      have h2 : ‖(g A : E m →L[ℝ] E m) - opOf B.1‖ < θ/2 := by
        rw [hval, norm_sub_rev]
        exact hg B
      have htri : ‖opOf A.1 - opOf B.1‖
          ≤ ‖opOf A.1 - (g A : E m →L[ℝ] E m)‖
            + ‖(g A : E m →L[ℝ] E m) - opOf B.1‖ := by
        have ht := dist_triangle (opOf A.1) (g A : E m →L[ℝ] E m) (opOf B.1)
        rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at ht
      linarith
    have hfar : θ ≤ ‖opOf A.1 - opOf B.1‖ := hS A.1 A.2 B.1 B.2 hAne
    linarith
  haveI : Fintype ↥S := Fintype.ofInjective g hinj
  refine ⟨Set.finite_def.mpr ⟨inferInstance⟩, ?_⟩
  rw [← Set.fintypeCard_eq_ncard S]
  calc Fintype.card ↥S ≤ Fintype.card ↥F := Fintype.card_le_of_injective g hinj
    _ = F.card := Fintype.card_coe F

end Work.Mostow
