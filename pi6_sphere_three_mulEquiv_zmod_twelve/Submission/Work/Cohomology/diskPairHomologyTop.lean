import Mathlib
import Submission.Work.Cohomology.DiskPairBasic
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereInUnitHomologyIso
import Submission.Work.Cohomology.diskPairHomologyTopOne

/-!
# The top relative homology of the disk pair `(Dⁿ, Sⁿ⁻¹)`

We compute `Hₙ(Dⁿ, Sⁿ⁻¹; ℤ) ≅ ℤ` for `n ≥ 1` — the degree-`n` "local homology" input of the
Thom isomorphism for a trivial rank-`n` bundle, and the first genuine local-homology computation
of the cohomology chapter.

The proof uses the long exact sequence of the pair `(Dⁿ, Sⁿ⁻¹)` (`Work.Cohomology.hPair_exact₁/₃`):

`Hₙ(Dⁿ) ⟶ Hₙ(Dⁿ, Sⁿ⁻¹) ⟶ Hₙ₋₁(Sⁿ⁻¹) ⟶ Hₙ₋₁(Dⁿ)`,

in which the outer terms vanish for `n ≥ 2` because `Dⁿ` is contractible
(`Work.Cohomology.homologyContractible`).  Hence the connecting map `hPairδ` is an isomorphism
and `Hₙ(Dⁿ, Sⁿ⁻¹) ≅ Hₙ₋₁(Sⁿ⁻¹) ≅ ℤ` by `Work.Cohomology.sphereHomologyTop`.  The case `n = 1`
is different (the sequence stops at `H₀(S⁰)`, which is `ℤ²`); it is the separate lemma
`Work.Cohomology.diskPairHomologyTopOne`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- The closed unit ball `Dⁿ` is contractible (it is a nonempty convex subset of `ℝⁿ`). -/
theorem diskUnit_contractible (n : ℕ) : ContractibleSpace (diskUnit n) :=
  Convex.contractibleSpace (convex_closedBall 0 1) ⟨0, by simp [Metric.mem_closedBall]⟩

/-- **The connecting map of the disk pair is an isomorphism when the outer terms vanish.**

If `H_{m+1}(X) = 0` and `H_m(X) = 0`, then in the exact sequence

`H_{m+1}(X) ⟶ H_{m+1}(X,A) --δ--> H_m(A) ⟶ H_m(X)`

of the pair `(X,A)` the connecting map `δ = hPairδ X A m` is both injective and surjective. -/
theorem hPairδ_isIso (X : TopCat) (A : Set X) (m : ℕ)
    (h1 : IsZero ((singularChains ℤ X).homology (m + 1)))
    (h2 : IsZero ((singularChains ℤ X).homology m)) :
    IsIso (hPairδ X A m) := by
  -- exactness at `H_{m+1}(X,A)`: the incoming map out of a zero object is `0`, hence `δ` is mono
  have hf : (ShortComplex.mk
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X A)) (m + 1))
      (hPairδ X A m) (hPair_comp_δ X A m)).f = 0 :=
    h1.eq_of_src _ 0
  have hmono : Mono (hPairδ X A m) :=
    (ShortComplex.exact_iff_mono _ hf).1 (hPair_exact₃ X A m)
  -- exactness at `H_m(A)`: the outgoing map into a zero object is `0`, hence `δ` is epi
  have hg : (ShortComplex.mk (hPairδ X A m)
      (HomologicalComplex.homologyMap (inclChains X A) m)
      (hPairδ_comp X A m)).g = 0 := h2.eq_of_tgt _ 0
  have hepi : Epi (hPairδ X A m) :=
    (ShortComplex.exact_iff_epi _ hg).1 (hPair_exact₁ X A m)
  exact isIso_of_mono_of_epi _

/-- **The top relative homology of the disk pair `(Dⁿ, Sⁿ⁻¹)` is `ℤ`** (`n ≥ 1`). -/
theorem diskPairHomologyTop (n : ℕ) (hn : 1 ≤ n) :
    Nonempty
      ((Work.Cohomology.relChains (Work.Cohomology.diskUnit n)
        (Work.Cohomology.sphereInUnit n)).homology n ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel hn).symm⟩
  rcases m with _ | k
  · -- `n = 1`: the sequence involves `H₀(S⁰) ≅ ℤ²`, handled separately
    rw [hm]
    simpa using diskPairHomologyTopOne
  · -- `n = k + 2 ≥ 2`: the connecting map is an isomorphism onto `H_{k+1}(S^{k+1}) ≅ ℤ`
    rw [hm]
    haveI : ContractibleSpace (diskUnit (k + 1 + 1)) := diskUnit_contractible _
    have h1 : IsZero ((singularChains ℤ (diskUnit (k + 1 + 1))).homology ((k + 1) + 1)) :=
      homologyContractible ((k + 1) + 1) (by omega)
    have h2 : IsZero ((singularChains ℤ (diskUnit (k + 1 + 1))).homology (k + 1)) :=
      homologyContractible (k + 1) (by omega)
    haveI : IsIso (hPairδ (diskUnit (k + 1 + 1)) (sphereInUnit (k + 1 + 1)) (k + 1)) :=
      hPairδ_isIso (diskUnit (k + 1 + 1)) (sphereInUnit (k + 1 + 1)) (k + 1) h1 h2
    exact ⟨asIso (hPairδ (diskUnit (k + 1 + 1)) (sphereInUnit (k + 1 + 1)) (k + 1)) ≪≫
      (sphereInUnitHomologyIso (k + 1 + 1) (k + 1)).some ≪≫
      (sphereHomologyTop (k + 1) (by omega)).some⟩

end

end Work.Cohomology
