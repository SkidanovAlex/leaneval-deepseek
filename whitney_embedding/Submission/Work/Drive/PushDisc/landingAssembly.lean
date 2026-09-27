import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Whitney.SlabPushGuts

/-!
# The clause set from the *landing* form of the push

`Work.Drive.PushDisc.hasAmbientPushData_of_finger_off_image` (`PushDisc/sweepClauses.lean`) derives
the clause set from the **strong** hypothesis that every *moved* value of the finger is off the
whole image `f '' M`.  That form is *unusable* for the constructions actually available: the
collision analysis (`PushDisc/fingerEscape.lean`, `Drive/NOTES_CAP_STATE.md` §2) shows that a
position-modulated displacement always produces a collision, so the moved values can never all be
off the image.

The usable form is the **landing** condition: a moved value either is off the image, or is the image
of a point of `W₀` itself.  This file proves that this weaker condition, together with the exclusion
of the two double point values, already gives the whole clause set.

## Contents

* `Work.Drive.PushDisc.hasAmbientPushData_of_landing` — the assembly.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set

/-- **The landing form of the push gives the clause set.**

Let `W₀ ⊆ W` be open, `p₂, q₂ ∈ W₀`, `p₁, q₁ ∉ W₀`, `(ψ, σ)` a pair of smooth mutually inverse
self-maps of `ℝ^{2n}` which is the identity on an open `O ⊇ f '' frontier W₀`, such that

* every *moved* value of a point of `W₀` lands in `f '' W₀ ∪ (f '' M)ᶜ` (`hland`), and
* the two double values `f p₂`, `f q₂` are not attained on `f '' W₀` (`hnonat`),

then all five clauses of `Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂` hold.

The proof is purely combinatorial: the only nontrivial points are the two crossing pairs
`(p₂, p₁)` and `(q₂, q₁)`, which would put the value `f p₂` (resp. `f q₂`) into `ψ '' (f '' W₀)`,
and are excluded by `hnonat`. -/
theorem hasAmbientPushData_of_landing {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (W₀ : Set M) (hW₀o : IsOpen W₀) (hW₀W : W₀ ⊆ W)
    (hp₂ : p₂ ∈ W₀) (hq₂ : q₂ ∈ W₀) (hp₁ : p₁ ∉ W₀) (hq₁ : q₁ ∉ W₀)
    (O : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (hOo : IsOpen O) (hOfront : f '' frontier W₀ ⊆ O)
    (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (hOid : ∀ y, y ∈ O → ψ y = y)
    (hσψ : ∀ y, σ (ψ y) = y) (hψσ : ∀ y, ψ (σ y) = y)
    (hψsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hσsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hland : ∀ x ∈ W₀, ψ (f x) ≠ f x →
      ψ (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ)
    (hnonat : ∀ x ∈ W₀, ψ (f x) ≠ f p₂ ∧ ψ (f x) ≠ f q₂) :
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  refine Work.Whitney.hasAmbientPushData_of_separation f W p₁ p₂ q₁ q₂ hfp hfq W₀ O ψ σ
    hW₀o hW₀W hp₂ hq₂ hp₁ hq₁ hOo hOfront hOid hσψ hψσ hψsm hσsm ?_
  intro x hx z hψ
  by_cases hmov : ψ (f x) = f x
  · -- the source is fixed: the only preimages inside `W` are the source and the crossing partners
    have hfxz : f x = f z := hmov.symm.trans hψ
    have hzW : z ∈ W := by
      by_contra hzW
      exact hsep x z (hW₀W hx) hzW hfxz
    rcases hclean x z (hW₀W hx) hzW hfxz with h | h | h | h | h
    · exact h ▸ hx
    · exact absurd (h.1 ▸ hx) hp₁
    · exact absurd (show ψ (f x) = f p₂ by rw [hmov, h.1]) (hnonat x hx).1
    · exact absurd (h.1 ▸ hx) hq₁
    · exact absurd (show ψ (f x) = f q₂ by rw [hmov, h.1]) (hnonat x hx).2
  · -- the source is moved: either the value is off the image, or it is the image of some `w ∈ W₀`
    rcases hland x hx hmov with ⟨w, hw, hwz⟩ | hoff
    · have hzw : f z = f w := hψ.symm.trans hwz.symm
      by_cases hzW : z ∈ W
      · rcases hclean z w hzW (hW₀W hw) hzw with h | h | h | h | h
        · exact h ▸ hw
        · exact absurd (show ψ (f x) = f p₂ by rw [← hwz, h.2]) (hnonat x hx).1
        · exact absurd (h.2 ▸ hw) hp₁
        · exact absurd (show ψ (f x) = f q₂ by rw [← hwz, h.2]) (hnonat x hx).2
        · exact absurd (h.2 ▸ hw) hq₁
      · exact absurd hzw.symm (hsep w z (hW₀W hw) hzW)
    · exact absurd ⟨z, Set.mem_univ z, hψ.symm⟩ hoff

/-! ## The two-point fibre of a clean region -/

/-- **The fibre of the double value.**  In a clean region `W` whose only `f`-coincidences are the
four crossing pairs, the preimages of the double value `f p₁ = f p₂` inside all of `M` are exactly
`p₁` and `p₂`: inside `W` this is `hclean`, outside `W` it is `hsep`.  This is the `hpre` hypothesis
of `Work.Whitney.exists_isolation_radius` (`Whitney/twoStepIsolation.lean`), whose conclusion is the
local structure used by every push construction on disk: for small `δ`, the points `y` with
`‖f y - f p₁‖ < δ` all lie in the two sheet charts. -/
theorem eq_p₁_or_p₂_of_f_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) :
    ∀ y : M, f y = f p₁ → y = p₁ ∨ y = p₂ := by
  intro y hy
  by_cases hyW : y ∈ W
  · rcases hclean y p₁ hyW hW₁ hy with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact absurd h.2 hp₁q₂
    · exact absurd h.2 hp₁q₁
  · exact absurd hy.symm (hsep p₁ y hW₁ hyW)

end Work.Drive.PushDisc
