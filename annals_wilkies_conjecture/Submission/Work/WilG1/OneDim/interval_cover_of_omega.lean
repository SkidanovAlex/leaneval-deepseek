import Mathlib
import Submission.Work.Wilkies.Defs

/-!
# Covering an `Ω`-set in one dimension by preconnected sets of reals

`WilkiesDesign.SOMin.comps` is the (frozen) axiom that a set `A ⊆ ℝⁿ` in the format
`Ω F D n` has at most `p_F(D)` preconnected components, where `p_F` is a polynomial in the
degree bound `D` depending only on the format `F`.

This file is the one-dimensional instance of that axiom, stated for sets `X ⊆ ℝ¹` and
transported to sets of *reals* along the canonical identification `ℝ → (Fin 1 → ℝ)`,
so that consumers working on the real line can apply it directly.

The degree bound is not used at its "own" variable: the lemma is stated for an arbitrary
polynomial `b` and a natural number `D`, with `b.eval D` playing the role of the degree
bound.  Since a cover bound that depends polynomially on the degree bound is available,
applying `comps` at the value `b.eval D` gives exactly the required estimate.

The only mathematical content beyond `comps` is that the single coordinate of `Fin 1 → ℝ`
is a continuous section of `x ↦ (fun _ => x)`: hence images of preconnected sets are
preconnected, and the union of the cover is carried along.
-/

set_option autoImplicit false

noncomputable section

namespace Work.WilG1.OneDim

/-- The unique coordinate of a point of `ℝ¹ = Fin 1 → ℝ`. -/
private def coord (z : Fin 1 → ℝ) : ℝ := z 0

/-- The coordinate map is continuous. -/
private theorem coord_continuous : Continuous coord := continuous_apply 0

/-- The coordinate map is a section of the diagonal embedding `x ↦ (fun _ => x)`. -/
private theorem coord_section (z : Fin 1 → ℝ) : (fun _ : Fin 1 => coord z) = z := by
  funext i
  rw [Fin.eq_zero i]
  rfl

/-- The set of reals whose image under `x ↦ (fun _ : Fin 1 => x)` lies in `X` is the image of
`X` under the coordinate map. -/
private theorem setOf_coord_eq_image (X : Set (Fin 1 → ℝ)) :
    {x : ℝ | (fun _ : Fin 1 => x) ∈ X} = coord '' X := by
  ext x
  constructor
  · intro hx
    exact ⟨fun _ : Fin 1 => x, hx, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    show (fun _ : Fin 1 => coord z) ∈ X
    rwa [coord_section z]

theorem interval_cover_of_omega {S : WilkiesDesign.SOMin} {a : ℕ} :
    ∃ p : Polynomial ℕ, ∀ {D : ℕ} {b : Polynomial ℕ} {X : Set (Fin 1 → ℝ)},
      X ∈ S.Ω a (b.eval D) 1 →
      ∃ s : Finset (Set ℝ), s.card ≤ p.eval (b.eval D) ∧ (∀ I ∈ s, IsPreconnected I) ∧
        {x : ℝ | (fun _ : Fin 1 => x) ∈ X} = ⋃₀ (s : Set (Set ℝ)) := by
  classical
  obtain ⟨p, hp⟩ := S.comps a
  refine ⟨p, ?_⟩
  intro D b X hX
  obtain ⟨s, hcard, hpre, hsum⟩ := hp (b.eval D) X hX
  refine ⟨s.image (Set.image coord), ?_, ?_, ?_⟩
  · exact le_trans Finset.card_image_le hcard
  · intro I hI
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hI
    exact IsPreconnected.image (hpre J hJ) coord coord_continuous.continuousOn
  · rw [setOf_coord_eq_image X, hsum, Set.image_sUnion, Finset.coe_image]

end Work.WilG1.OneDim
