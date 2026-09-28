import Submission.Work.StemsB.WangSequence
import Submission.Work.StemsB.FibreTrivCohomology
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.sphereHomologyTop

/-!
# The Wang sequence in homology

The homological companion of `WangSequence.lean`.  For a topological space `X`, a subset `A ⊆ X`,
a space `F` and an integer `m`, the long exact sequence of the pair `(X,A)`

  `⋯ ⟶ Hₙ(A) ⟶ Hₙ(X) ⟶ Hₙ(X,A) --∂--> Hₙ₋₁(A) ⟶ ⋯`

together with the two identifications `γ : Hₙ(A) ≅ Hₙ(F)` and `τ : Hₙ(X,A) ≅ Hₙ₋ₘ(F)` gives the
**Wang sequence**

  `⋯ ⟶ Hₙ₊₁(X) → Hₙ₊₁₋ₘ(F) --θ--> Hₙ(F) ⟶ Hₙ(X) → Hₙ₋ₘ(F) ⟶ ⋯`

with `θ` the connecting homomorphism of the pair transported by `γ` and `τ`.  As in the
cohomological case (`Work.StemsB.wangExact₁/₂/₃`) the exactness is by construction.

Everything is indexed by `ℤ` and extended by `0` in negative degrees (`Work.StemsB.chainZ`), since
`τ` shifts by `m`.

This file also records the homological counterpart of
`Work.StemsB.nonempty_singularCohomology_iso_fibreTriv`: the triviality over a contractible `W`
identifies `H_n(p ⁻¹' W)` with `H_n` of the fibre.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

/-! ## The fibre identification in homology -/

/-- **Restriction to the fibre is an isomorphism in homology** when the map is fibrewise trivial
over a contractible `W`. -/
theorem nonempty_homologyIso_fibreTriv {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (W : Set B) (d₀ : ↥W) (hT : FibrewiseTrivial p W d₀) (w₀ : ↥W)
    (c : C(↥W × unitInterval, ↥W)) (hc0 : ∀ w, c (w, 0) = w) (hc1 : ∀ w, c (w, 1) = w₀)
    (n : ℕ) :
    Nonempty (((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' W))).homology n) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' {d₀.1}))).homology n)) := by
  obtain ⟨e₁⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv (fibTrivHomotopyEquiv p W d₀ hT) n
  obtain ⟨e₂⟩ := Work.Cohomology.homologyIso_of_homotopyEquiv
    (prodSndHomotopyEquiv ↥(p ⁻¹' {d₀.1}) ↥W w₀ c hc0 hc1) n
  exact ⟨e₁ ≪≫ e₂⟩

/-! ## The graded groups -/

/-- Singular homology, indexed by `ℤ` and extended by `0` in negative degrees. -/
noncomputable def chainZ (X : TopCat) : ℤ → ModuleCat ℤ
  | ((n : ℕ) : ℤ) => (Work.Cohomology.singularChains ℤ X).homology n
  | _ => zeroModZ

@[simp] theorem chainZ_nat (X : TopCat) (n : ℕ) :
    chainZ X (n : ℤ) = (Work.Cohomology.singularChains ℤ X).homology n := rfl

/-! ## The Wang sequence -/

/-- The map `H_n(F) ⟶ H_n(X)` of the Wang sequence. -/
def wangHomα (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ n : ℕ, (Work.Cohomology.singularChains ℤ (TopCat.of A)).homology n ≅ chainZ Fsp n)
    (n : ℕ) : chainZ Fsp (n : ℤ) ⟶ chainZ X (n : ℤ) :=
  (γ n).inv ≫ HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) n

/-- The map `H_n(X) ⟶ H_{n-m}(F)` of the Wang sequence. -/
def wangHomβ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (τ : ∀ k : ℕ, (Work.Cohomology.relChains X A).homology k ≅ chainZ Fsp ((k : ℤ) - (m : ℤ)))
    (n : ℕ) : chainZ X (n : ℤ) ⟶ chainZ Fsp ((n : ℤ) - (m : ℤ)) :=
  HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) n ≫ (τ n).hom

/-- The map `θ : H_{n+1-m}(F) ⟶ H_n(F)` of the Wang sequence. -/
def wangHomθ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ n : ℕ, (Work.Cohomology.singularChains ℤ (TopCat.of A)).homology n ≅ chainZ Fsp n)
    (τ : ∀ k : ℕ, (Work.Cohomology.relChains X A).homology k ≅ chainZ Fsp ((k : ℤ) - (m : ℤ)))
    (n : ℕ) : chainZ Fsp (((n + 1 : ℕ) : ℤ) - (m : ℤ)) ⟶ chainZ Fsp (n : ℤ) :=
  (τ (n + 1)).inv ≫ Work.Cohomology.hPairδ X A n ≫ (γ n).hom

/-- **Exactness of the Wang sequence at `H_n(X)`**. -/
theorem wangHomExact₁ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ n : ℕ, (Work.Cohomology.singularChains ℤ (TopCat.of A)).homology n ≅ chainZ Fsp n)
    (τ : ∀ k : ℕ, (Work.Cohomology.relChains X A).homology k ≅ chainZ Fsp ((k : ℤ) - (m : ℤ)))
    (n : ℕ) : Function.Exact (wangHomα X A Fsp m γ n) (wangHomβ X A Fsp m τ n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.hPair_exact₂ X A n)
  exact functionExact_conj (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) n)
    (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) n)
    (γ n) (Iso.refl (chainZ X (n : ℤ))) (τ n) h

/-- **Exactness of the Wang sequence at `H_{n+1-m}(F)`**. -/
theorem wangHomExact₂ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ n : ℕ, (Work.Cohomology.singularChains ℤ (TopCat.of A)).homology n ≅ chainZ Fsp n)
    (τ : ∀ k : ℕ, (Work.Cohomology.relChains X A).homology k ≅ chainZ Fsp ((k : ℤ) - (m : ℤ)))
    (n : ℕ) : Function.Exact (wangHomβ X A Fsp m τ (n + 1)) (wangHomθ X A Fsp m γ τ n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.hPair_exact₃ X A n)
  exact functionExact_conj
    (HomologicalComplex.homologyMap (cokernel.π (Work.Cohomology.inclChains X A)) (n + 1))
    (Work.Cohomology.hPairδ X A n)
    (Iso.refl (chainZ X (((n + 1 : ℕ) : ℤ)))) (τ (n + 1)) (γ n) h

/-- **Exactness of the Wang sequence at `H_n(F)`**. -/
theorem wangHomExact₃ (X : TopCat) (A : Set X) (Fsp : TopCat) (m : ℕ)
    (γ : ∀ n : ℕ, (Work.Cohomology.singularChains ℤ (TopCat.of A)).homology n ≅ chainZ Fsp n)
    (τ : ∀ k : ℕ, (Work.Cohomology.relChains X A).homology k ≅ chainZ Fsp ((k : ℤ) - (m : ℤ)))
    (n : ℕ) : Function.Exact (wangHomθ X A Fsp m γ τ n) (wangHomα X A Fsp m γ n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (Work.Cohomology.hPair_exact₁ X A n)
  exact functionExact_conj (Work.Cohomology.hPairδ X A n)
    (HomologicalComplex.homologyMap (Work.Cohomology.inclChains X A) n)
    (τ (n + 1)) (γ n) (Iso.refl (chainZ X (n : ℤ))) h

end

end Work.StemsB
