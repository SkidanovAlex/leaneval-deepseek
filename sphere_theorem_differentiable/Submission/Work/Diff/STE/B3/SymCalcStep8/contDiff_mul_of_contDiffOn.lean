import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

/-- The product of a function that is `C^∞` on an open set `W` with a smooth bump whose
topological support lies in `W` is globally `C^∞`.

(No hypothesis on `f` outside `W` is needed: at a point `p ∉ W` we have `p ∉ tsupport φ`, so `φ`
vanishes on a whole neighbourhood of `p`, while on `W` the product is a product of smooth
functions.  Suitable gluing lemma: `contDiff_of_contDiffOn_union_of_isOpen`.) -/
theorem contDiff_mul_of_contDiffOn {ι : Type*} [Fintype ι]
    (W : Set (ι → ℝ)) (hW : IsOpen W) (f : (ι → ℝ) → ℂ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f W)
    (φ : (ι → ℝ) → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hsup : tsupport φ ⊆ W) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z * f z) := by
  -- `W` and the complement of `tsupport φ` are open and cover the whole space, and on each of
  -- them the product is smooth: on `W` it is a product of smooth functions, and on the
  -- complement of `tsupport φ` the factor `φ` vanishes identically.
  have hcover : W ∪ (tsupport φ)ᶜ = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ W
    · exact Or.inl hx
    · exact Or.inr fun hmem => hx (hsup hmem)
  refine contDiff_of_contDiffOn_union_of_isOpen (t := (tsupport φ)ᶜ) ?_ ?_ hcover hW
    (isClosed_tsupport φ).isOpen_compl
  · exact ContDiffOn.mul hφ.contDiffOn hf
  · refine ContDiffOn.congr (s := (tsupport φ)ᶜ) (f := fun _ => (0 : ℂ)) ?_ ?_
    · exact contDiffOn_const
    · intro x hx
      show φ x * f x = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

end Work.Diff.STE.B3.SymCalcStep8
