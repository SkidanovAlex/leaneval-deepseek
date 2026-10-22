import Mathlib
import Submission.Work.ANALYTIC.BoundedType

/-!
# Injectivity of the comparison map of `∏^bnd ℤ` along a surjection

If `π : X ⟶ B` is a surjective map of light profinite sets, then the comparison map
`boundedTypePresheaf.map π.op : boundedSeqSet B ⟶ boundedSeqSet X` (which is just precomposition
of uniformly bounded sequences of continuous `ℤ`-valued functions with `π`) is injective: two
sequences that agree after pulling back along a surjection already agree.
-/

namespace Work.ANALYTIC

/-- The comparison map of `boundedTypePresheaf` along `π : X ⟶ B` is precomposition with `π`:
`(π^* a)_n = a_n ∘ π`. -/
lemma boundedTypePresheaf_map_apply {X B : LightProfinite} (π : X ⟶ B) (a : boundedSeqSet B)
    (n : ℕ) (x : X) :
    ((boundedTypePresheaf.map π.op a : boundedSeqSet X).1 n) x = (a.1 n) (π x) := rfl

theorem boundedSeq_map_injective {X B : LightProfinite} (π : X ⟶ B)
    (hπ : ∀ y : B, ∃ x : X, π x = y) (a b : boundedSeqSet B)
    (h : boundedTypePresheaf.map π.op a = boundedTypePresheaf.map π.op b) : a = b := by
  apply Subtype.ext
  funext n
  ext y
  obtain ⟨x, rfl⟩ := hπ y
  have h' : (boundedTypePresheaf.map π.op a : boundedSeqSet X) =
      (boundedTypePresheaf.map π.op b : boundedSeqSet X) := h
  have hx := congrArg (fun z : boundedSeqSet X => (z.1 n) x) h'
  rw [boundedTypePresheaf_map_apply, boundedTypePresheaf_map_apply] at hx
  exact hx

end Work.ANALYTIC
