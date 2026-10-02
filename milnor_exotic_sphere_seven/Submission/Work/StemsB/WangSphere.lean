import Submission.Work.StemsB.WangSequence
import Submission.Work.StemsB.FibreTrivCohomology
import Submission.Work.StemsB.SerreSphereAssembly

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Wang sequence over the sphere model

This file instantiates the abstract Wang sequence of `WangSequence.lean` for a map
`p : E → SphModel m` whose value at the base point is the fibre.  The two discs of the model are
`sphLoopOuter m` (containing `∞`) and `sphLoopBig m` (the inner cube); the Wang sequence is the long
exact sequence of the pair `(E, E|_(sphLoopBig m))`, read through

* `γ` — the identification `H^n(E|_(sphLoopBig m)) ≅ H^n(fibre)`, built here from the fibrewise
  triviality over the contractible inner cube (`nonempty_singularCohomology_iso_fibreTriv`), and
* `τ` — the identification `H^n(E, E|_(sphLoopBig m)) ≅ H^(n-m)(fibre)`, which is excision plus the
  disc-pair computation; it is the hypothesis `τ` of the statement below (it does not depend on the
  geometry of the model, only on the pair `(D^m, ∂D^m)`).

The conclusion is the exactness of the Wang sequence

  `H^q(E) → H^q(F) --θ--> H^(q+1-m)(F) → H^(q+1)(E)`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-- **The `γ` of the Wang sequence over the inner cube**: the identification of `H^q(E|_V)` with the
cohomology of the fibre, for `V = sphLoopBig m`. -/
def wangGammaSphere (m : ℕ) (hm : 1 ≤ m) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel m)) (d₀ : ↥(sphLoopBig m)) (hc : sphShellPt m ∈ sphLoopBig m)
    (hT : FibrewiseTrivial p (sphLoopBig m) d₀) :
    ∀ q : ℕ, Work.Cohomology.singularCohomology ℤ q (TopCat.of (p ⁻¹' sphLoopBig m)) ≅
      cohZ (TopCat.of ↥(p ⁻¹' {d₀.1})) q := by
  intro q
  obtain ⟨hc0, hc1, _⟩ := Classical.choose_spec (serreSphere_contract_big m hm hc)
  exact Classical.choice (nonempty_singularCohomology_iso_fibreTriv p (sphLoopBig m) d₀ hT
    ⟨sphShellPt m, hc⟩ (Classical.choose (serreSphere_contract_big m hm hc)) hc0 hc1 q)

/-- **The Wang sequence over the sphere, in cohomology.**  For `p : E → SphModel m`, a fibrewise
triviality over the inner cube `sphLoopBig m`, and the identification `τ` of
`H^k(E, E|_(sphLoopBig m))` with `H^(k-m)(F)` (`F` the fibre over `d₀`), the sequence

  `H^q(E) → H^q(F) --θ--> H^(q+1-m)(F) → H^(q+1)(E)`

is exact, `θ` being the connecting homomorphism of the pair `(E, E|_(sphLoopBig m))` transported by
`γ` and `τ`. -/
theorem wangSequence_sphere (m : ℕ) (hm : 1 ≤ m) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel m)) (d₀ : ↥(sphLoopBig m)) (hc : sphShellPt m ∈ sphLoopBig m)
    (hT : FibrewiseTrivial p (sphLoopBig m) d₀)
    (τ : ∀ k : ℕ, Work.Cohomology.relCohomology ℤ (TopCat.of E) (p ⁻¹' sphLoopBig m) k ≅
      cohZ (TopCat.of ↥(p ⁻¹' {d₀.1})) ((k : ℤ) - (m : ℤ))) (q : ℕ) :
    Function.Exact
        (wangα (TopCat.of E) (p ⁻¹' sphLoopBig m) (TopCat.of ↥(p ⁻¹' {d₀.1})) m
          (wangGammaSphere m hm E p d₀ hc hT) q)
        (wangθ (TopCat.of E) (p ⁻¹' sphLoopBig m) (TopCat.of ↥(p ⁻¹' {d₀.1})) m
          (wangGammaSphere m hm E p d₀ hc hT) τ q)
      ∧ Function.Exact
        (wangθ (TopCat.of E) (p ⁻¹' sphLoopBig m) (TopCat.of ↥(p ⁻¹' {d₀.1})) m
          (wangGammaSphere m hm E p d₀ hc hT) τ q)
        (wangβ (TopCat.of E) (p ⁻¹' sphLoopBig m) (TopCat.of ↥(p ⁻¹' {d₀.1})) m τ q)
      ∧ Function.Exact
        (wangβ (TopCat.of E) (p ⁻¹' sphLoopBig m) (TopCat.of ↥(p ⁻¹' {d₀.1})) m τ q)
        (wangα (TopCat.of E) (p ⁻¹' sphLoopBig m) (TopCat.of ↥(p ⁻¹' {d₀.1})) m
          (wangGammaSphere m hm E p d₀ hc hT) (q + 1)) :=
  ⟨wangExact₁ _ _ _ _ _ τ q, wangExact₂ _ _ _ _ _ τ q, wangExact₃ _ _ _ _ _ τ q⟩

end

end Work.StemsB
