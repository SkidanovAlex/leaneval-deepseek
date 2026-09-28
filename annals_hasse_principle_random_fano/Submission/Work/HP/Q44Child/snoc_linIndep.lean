import Mathlib
import Submission.Work.HP.Defs

set_option linter.style.haveILetI false

namespace Work.HP.Q44Child

/-- Given `k` ℤ-linearly independent vectors `f` and `k+1` ℤ-linearly independent vectors `g`
in the free ℤ-module `ι → ℤ`, one of the vectors `g t` can be appended to `f` while keeping
ℤ-linear independence.

The proof passes to the ℚ-vector space `ι → ℚ`: the images of the `g t` span a `(k+1)`-dimensional
subspace, which cannot be contained in the `k`-dimensional span of the images of `f`. -/
theorem snoc_linIndep {ι : Type*} [Fintype ι] {k : ℕ} {f : Fin k → (ι → ℤ)} {g : Fin (k + 1) → (ι → ℤ)}
    (hf : LinearIndependent ℤ f) (hg : LinearIndependent ℤ g) :
    ∃ t : Fin (k + 1), LinearIndependent ℤ (Fin.snoc f (g t)) := by
  -- Pass to the ℚ-vector space `ι → ℚ` via the componentwise map `algebraMap ℤ ℚ`.
  let F : Fin k → (ι → ℚ) := fun i => ⇑(algebraMap ℤ ℚ) ∘ f i
  let G : Fin (k + 1) → (ι → ℚ) := fun t => ⇑(algebraMap ℤ ℚ) ∘ g t
  have hF : LinearIndependent ℚ F :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).mpr hf
  have hG : LinearIndependent ℚ G :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)).mpr hg
  -- Some `G t` must lie outside the `k`-dimensional span of `F`.
  have hex : ∃ t, G t ∉ Submodule.span ℚ (Set.range F) := by
    by_contra h
    have hmem : ∀ t, G t ∈ Submodule.span ℚ (Set.range F) := fun t => by
      by_contra ht; exact h ⟨t, ht⟩
    have hle : Submodule.span ℚ (Set.range G) ≤ Submodule.span ℚ (Set.range F) := by
      rw [Submodule.span_le]
      rintro x ⟨t, rfl⟩
      exact hmem t
    haveI : Module.Finite ℚ ↥(Submodule.span ℚ (Set.range F)) :=
      Module.Finite.span_of_finite ℚ (Set.finite_range F)
    have hlt : (k + 1 : ℕ) ≤ k := by
      have hmono := Submodule.finrank_mono hle
      rw [finrank_span_eq_card hG, finrank_span_eq_card hF] at hmono
      simpa only [Fintype.card_fin] using hmono
    omega
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ?_⟩
  -- ℤ-independence of `Fin.snoc f (g t)` is equivalent to ℚ-independence of its image.
  rw [← (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ)
        (v := (Fin.snoc f (g t) : Fin (k + 1) → (ι → ℤ))))]
  have heq : (fun i => ⇑(algebraMap ℤ ℚ) ∘ ((Fin.snoc f (g t) : Fin (k + 1) → (ι → ℤ)) i))
      = Fin.snoc F (G t) := by
    ext i
    induction i using Fin.lastCases with
    | last => simp [F, G]
    | cast j => simp [F, G]
  rw [heq]
  exact LinearIndependent.finSnoc hF ht

end Work.HP.Q44Child
