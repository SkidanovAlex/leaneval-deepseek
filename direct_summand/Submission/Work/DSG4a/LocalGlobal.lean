import Mathlib
import Submission.Work.DSG4a.Split

/-!
# DSG4a: local-to-global for the splitting ideal

The last step of the local-to-global argument is purely ideal-theoretic: an element of an
ideal `I` of a commutative ring `A` which lands in `I · A'` for a flat local `A'` over every
maximal ideal is already in `I`.  The point is that `I · A' ⊆ 𝔪'` when `𝔪'` lies over a
maximal ideal `𝔪 ⊇ I` — *only flatness and lying over are used*, no faithful flatness.

The module-level local-to-global theorem is `isUnimodular_of_forall_maximal` in
`Submission.Work.DSG4a.PresentLocalGlobal`: it combines this lemma with
`one_mem_map_splitIdeal_of_isUnimodular` (the flat base change of the splitting ideal of a
presented module), which is where the real content of the area sits.
-/

namespace Work.DSG4a

universe u

/-- **Local-to-global for ideals.**  Let `I` be an ideal of `A` such that for every maximal
ideal `𝔪` there is a flat local `A → A'` with `(maximalIdeal A').comap ψ = 𝔪` and
`1 ∈ I · A'`.  Then `1 ∈ I`.

Only flatness and the lying-over condition are used (via `I · A' ⊆ 𝔪'`); no faithful
flatness and no finiteness. -/
theorem one_mem_ideal_of_forall_maximal {A : Type u} [CommRing A] (I : Ideal A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → ∃ (A' : Type u) (_ : CommRing A') (_ : IsLocalRing A')
      (ψ : A →+* A'), ψ.Flat ∧ (IsLocalRing.maximalIdeal A').comap ψ = 𝔪 ∧ (1 : A') ∈ I.map ψ) :
    1 ∈ I := by
  by_contra h1
  obtain ⟨𝔪, h𝔪max, hI𝔪⟩ := Ideal.exists_le_maximal I (Ideal.ne_top_iff_one I |>.mpr h1)
  obtain ⟨A', _, _, ψ, -, hcomap, hmem⟩ := h 𝔪 h𝔪max
  have hle : I.map ψ ≤ IsLocalRing.maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap, hcomap]
    exact hI𝔪
  have htop : IsLocalRing.maximalIdeal A' = ⊤ :=
    Ideal.eq_top_iff_one _ |>.mpr (hle hmem)
  exact h𝔪max.ne_top (hcomap ▸ congrArg (Ideal.comap ψ) htop)

end Work.DSG4a
