import Mathlib
import Submission.Work.TMComp.IDSDefs

namespace Work.TMComp.IDSBox

open Polynomial Matrix

/-- For a Hermitian complex matrix `A` whose characteristic polynomial is the
complexification of a real polynomial `p`, the number of eigenvalues of `A` below a
real threshold `X` (counted with multiplicity, i.e. by the index set `Fin n`) equals
the number of real roots of `p` below `X` (counted with multiplicity). -/
theorem eigroot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (p : Polynomial ℝ)
    (hchar : A.charpoly = p.map (algebraMap ℝ ℂ)) :
    ∀ X : ℝ, ((Finset.univ.filter (fun k : Fin n => hA.eigenvalues k < X)).card : ℝ)
      = ((p.roots.filter (fun r => r < X)).card : ℝ) := by
  classical
  -- The complexification map `ℝ → ℂ` is injective.
  have hf : Function.Injective (algebraMap ℝ ℂ) := Complex.ofReal_injective
  -- The roots of `p.map (algebraMap ℝ ℂ)` are exactly the images of the eigenvalues.
  have hmap : (p.map (algebraMap ℝ ℂ)).roots
      = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
    rw [← hchar, hA.roots_charpoly_eq_eigenvalues]
  -- Consequently every root of `p.map (algebraMap ℝ ℂ)` lies in the range of the map.
  have hrange : ∀ b ∈ (p.map (algebraMap ℝ ℂ)).roots, b ∈ (algebraMap ℝ ℂ).range := by
    intro b hb
    rw [hmap] at hb
    simp only [Multiset.mem_map, Function.comp_apply] at hb
    obtain ⟨k, _, rfl⟩ := hb
    exact ⟨hA.eigenvalues k, rfl⟩
  have hfilter : Multiset.filter (· ∈ (algebraMap ℝ ℂ).range) (p.map (algebraMap ℝ ℂ)).roots
      = (p.map (algebraMap ℝ ℂ)).roots :=
    Multiset.filter_eq_self.mpr hrange
  -- Hence the images of the roots of `p` are the roots of `p.map (algebraMap ℝ ℂ)`.
  have h1 : p.roots.map (algebraMap ℝ ℂ) = (p.map (algebraMap ℝ ℂ)).roots := by
    rw [← Polynomial.filter_roots_map_range_eq_map_roots hf p, hfilter]
  -- Compare with the eigenvalues: the two multisets are equal after mapping to `ℂ`.
  have h2 : p.roots.map (algebraMap ℝ ℂ)
      = Multiset.map (algebraMap ℝ ℂ) (Finset.univ.val.map hA.eigenvalues) := by
    rw [h1, hmap, Multiset.map_map]
  -- Injectivity of `Multiset.map` gives equality of the real multisets.
  have hroots : p.roots = Finset.univ.val.map hA.eigenvalues :=
    Multiset.map_injective hf h2
  intro X
  -- Counting the entries below `X` in a multiset is preserved by the multiset equality.
  have key : (Finset.univ.filter (fun k : Fin n => hA.eigenvalues k < X)).card
      = ((p.roots.filter (fun r => r < X))).card := by
    rw [hroots, Multiset.filter_map, Multiset.card_map]
    rw [← Finset.card_val, Finset.filter_val]
    exact congrArg Multiset.card
      (Multiset.filter_congr (s := Finset.univ.val) (fun k _ => Iff.rfl))
  exact_mod_cast key

end Work.TMComp.IDSBox
