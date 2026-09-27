import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.PushDisc.fingerRegion
import Submission.Work.Whitney.SlabPushGuts

/-!
# §6 of the cap design: the cap data gives the clause set

This is the combinatorial half of the *sweep*: given the finger `W₀`
(`Work.Drive.PushDisc.exists_finger_region_clean`) and an ambient diffeomorphism pair `(ψ, σ)` whose
**moved values are off the image**

    (cap)   ∀ x ∈ W₀, ψ (f x) ≠ f x → ψ (f x) ∉ f '' M ,

which is condition (3) of `Drive/NOTES_NOGO_MODULATED_TRANSLATION.md` §6, the five clauses of
`Work.Whitney.HasAmbientPushData` follow.  There are only three things to check:

* *separation*: a *moved* source has no preimage at all by (cap); an *unmoved* source `x` with
  `ψ (f x) = f x = f z` has `z ∈ W` (`hsep`), and `hclean` then leaves only `z = x` — the four
  crossing pairs force `x ∈ {p₁, q₁} ⊆ W₀ᶜ` or `x ∈ {p₂, q₂}`, which are *moved* (hypotheses
  `hp₂moved`, `hq₂moved`, supplied in §6 by "`β = 1` near `f p₂` and `f q₂`");
* *non-attainment* and *placement* then come from `Work.Whitney.hasAmbientPushData_of_separation`.

So the whole remaining geometric content is the construction of `(ψ, σ)` from the cap, i.e. the
*finger sweep*, and it is precisely there that the opposite-sign hypothesis is spent (the two ends'
landings must be coherent, `Whitney/NOTES_SBP_ISOTOPY_EXTENSION_ROUTE.md` §15).
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set

/-- **The cap data gives the clause set.**  With `W₀` a finger on which `f` is injective, an ambient
diffeomorphism pair `(ψ, σ)` which is the identity near `f '' frontier W₀`, which moves `f p₂` and
`f q₂`, and whose moved values are off `f '' M`, the Whitney push exists. -/
theorem hasAmbientPushData_of_finger_off_image {n : ℕ} {M : Type*} [TopologicalSpace M]
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
    (hinjW₀ : ∀ x ∈ W₀, ∀ y ∈ W₀, f x = f y → x = y)
    (ψ σ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)))
    (O : Set (EuclideanSpace ℝ (Fin (2 * n))))
    (hOo : IsOpen O) (hOfront : f '' frontier W₀ ⊆ O) (hOid : ∀ y, y ∈ O → ψ y = y)
    (hσψ : ∀ y, σ (ψ y) = y) (hψσ : ∀ y, ψ (σ y) = y)
    (hψsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hσsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) σ)
    (hmoved : ∀ x ∈ W₀, ψ (f x) ≠ f x → ψ (f x) ∉ f '' (Set.univ : Set M))
    (hp₂moved : ψ (f p₂) ≠ f p₂) (hq₂moved : ψ (f q₂) ≠ f q₂) :
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  refine Work.Whitney.hasAmbientPushData_of_separation f W p₁ p₂ q₁ q₂ hfp hfq W₀ O ψ σ
    hW₀o hW₀W hp₂ hq₂ hp₁ hq₁ hOo hOfront hOid hσψ hψσ hψsm hσsm ?_
  intro x hx z hz
  by_cases hmov : ψ (f x) = f x
  · -- the source is fixed: the only preimage inside `W` is the source itself
    have hfxz : f x = f z := hmov.symm.trans hz
    have hzW : z ∈ W := by
      by_contra hzW
      exact hsep x z (hW₀W hx) hzW hfxz
    rcases hclean x z (hW₀W hx) hzW hfxz with h | h | h | h | h
    · exact h ▸ hx
    · exact absurd (h.1 ▸ hx) hp₁
    · exact absurd (h.1 ▸ hmov) hp₂moved
    · exact absurd (h.1 ▸ hx) hq₁
    · exact absurd (h.1 ▸ hmov) hq₂moved
  · -- the source is moved: its value is off the image, so there is no preimage
    exact absurd ⟨z, Set.mem_univ z, hz.symm⟩ (hmoved x hx hmov)

end Work.Drive.PushDisc
