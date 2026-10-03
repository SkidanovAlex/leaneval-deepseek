import Mathlib

/-!
# Two sheets over the same preconnected base that meet are equal

`Work.Horn.sheets_eq_of_inter`.  Shishikura's construction of the horn map (Prop. 5.3) uses
repeatedly that a map `E : ℂ → ℂ` cannot have two *different* sheets over the same connected
base: if `φ` and `ψ` are homeomorphisms of open sets `V`, `W` onto a common preconnected set `O`
and both are given by `E` on their domains, then `V` and `W` coincide as soon as they meet.

The argument is purely topological (no regularity of `E` is used):

* `h := ψ⁻¹ ∘ φ : ↥V ≃ₜ ↥W` is a homeomorphism, and `h` fixes every point of `V ∩ W` (there
  `φ v = E v = ψ v` as elements of `O`).
* Hence `A := {v : ↥V | (v : ℂ) ∈ W}` agrees with the fixed point set
  `{v : ↥V | (h v : ℂ) = (v : ℂ)}`, which is closed in `↥V` (a preimage of `{0}` under a
  continuous map); and `A` is open in `↥V` because `W` is open.
* `↥V` is preconnected since `φ.symm : ↥O → ↥V` is surjective out of the preconnected `↥O`, so
  the nonempty clopen set `A` is all of `↥V`, i.e. `V ⊆ W`.  Swapping the roles of `φ, ψ` gives
  `W ⊆ V`.
-/

set_option linter.style.haveILetI false

namespace Work.Horn

/-- If a homeomorphism `f : ↥V ≃ₜ ↥W` between the subtypes of two subsets of `ℂ` fixes pointwise
the points of `V ∩ W` (as complex numbers) and `V` is preconnected, then `V ⊆ W`. -/
private lemma subset_of_homeo_fixing {V W : Set ℂ} (hVc : IsPreconnected V) (hW : IsOpen W)
    (f : ↥V ≃ₜ ↥W) (hfix : ∀ v : ↥V, (v : ℂ) ∈ W → (f v : ℂ) = (v : ℂ))
    (hne : (V ∩ W).Nonempty) : V ⊆ W := by
  haveI : PreconnectedSpace ↥V := Subtype.preconnectedSpace hVc
  -- the set of points of `V` lying in `W` is the fixed point set of `f`
  have hset : {v : ↥V | (v : ℂ) ∈ W} = {v : ↥V | (f v : ℂ) = (v : ℂ)} := by
    ext v
    constructor
    · exact hfix v
    · intro hv
      have h1 : (f v : ℂ) ∈ W := (f v).2
      rwa [hv] at h1
  have hclopen : IsClopen {v : ↥V | (v : ℂ) ∈ W} := by
    refine ⟨?_, hW.preimage continuous_subtype_val⟩
    rw [hset]
    exact isClosed_eq (continuous_subtype_val.comp f.continuous) continuous_subtype_val
  obtain ⟨x, hxV, hxW⟩ := hne
  have hne' : {v : ↥V | (v : ℂ) ∈ W}.Nonempty := ⟨⟨x, hxV⟩, hxW⟩
  have huniv : {v : ↥V | (v : ℂ) ∈ W} = Set.univ := by
    rcases isClopen_iff.mp hclopen with h | h
    · rw [h] at hne'; exact absurd hne' Set.not_nonempty_empty
    · exact h
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥V) ∈ {v : ↥V | (v : ℂ) ∈ W} := by rw [huniv]; exact Set.mem_univ _
  exact hy'

/-- Two "sheets" over the same preconnected base set that meet are equal: if `E` restricts to
homeomorphisms `V ≅ O` and `W ≅ O`, and `V ∩ W ≠ ∅`, then `V = W`. -/
theorem sheets_eq_of_inter {E : ℂ → ℂ} {O V W : Set ℂ} (hO : IsPreconnected O)
    (hV : IsOpen V) (hW : IsOpen W)
    (φ : ↥V ≃ₜ ↥O) (hφ : ∀ v : ↥V, (φ v : ℂ) = E (v : ℂ))
    (ψ : ↥W ≃ₜ ↥O) (hψ : ∀ w : ↥W, (ψ w : ℂ) = E (w : ℂ))
    (hne : (V ∩ W).Nonempty) : V = W := by
  -- preconnectedness of the sheets, transported from the base `O` along `φ.symm` and `ψ.symm`
  haveI : PreconnectedSpace ↥O := Subtype.preconnectedSpace hO
  have hVc : IsPreconnected V :=
    isPreconnected_iff_preconnectedSpace.mpr
      (DenseRange.preconnectedSpace φ.symm.surjective.denseRange φ.symm.continuous)
  have hWc : IsPreconnected W :=
    isPreconnected_iff_preconnectedSpace.mpr
      (DenseRange.preconnectedSpace ψ.symm.surjective.denseRange ψ.symm.continuous)
  -- the change of sheet `h = ψ⁻¹ ∘ φ : ↥V ≃ₜ ↥W`
  let h : ↥V ≃ₜ ↥W := φ.trans ψ.symm
  -- `h` fixes `V ∩ W` pointwise, because `φ` and `ψ` are both given by `E` there
  have hfix : ∀ v : ↥V, (v : ℂ) ∈ W → (h v : ℂ) = (v : ℂ) := by
    intro v hv
    have key : ψ (⟨(v : ℂ), hv⟩ : ↥W) = ψ (h v) := by
      apply Subtype.ext
      rw [hψ, hψ]
      have h1 : (ψ (h v) : ℂ) = (φ v : ℂ) := by
        simp only [h, Homeomorph.trans_apply]
        exact congrArg Subtype.val (ψ.apply_symm_apply (φ v))
      rw [hψ, hφ] at h1
      exact h1.symm
    exact (congrArg Subtype.val (ψ.injective key)).symm
  have h1 : V ⊆ W := subset_of_homeo_fixing hVc hW h hfix hne
  obtain ⟨x, hxV, hxW⟩ := hne
  have hne' : (W ∩ V).Nonempty := ⟨x, hxW, hxV⟩
  -- the symmetric statement for `h.symm = φ⁻¹ ∘ ψ`
  have hfix' : ∀ w : ↥W, (w : ℂ) ∈ V → (h.symm w : ℂ) = (w : ℂ) := by
    intro w _
    have hmem : ((h.symm w : ↥V) : ℂ) ∈ W := h1 (h.symm w).2
    have h2 := hfix (h.symm w) hmem
    rw [h.apply_symm_apply w] at h2
    exact h2.symm
  exact Set.Subset.antisymm h1 (subset_of_homeo_fixing hWc hV h.symm hfix' hne')

end Work.Horn
