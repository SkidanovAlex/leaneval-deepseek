import Mathlib
import Submission.Work.Gen.Euler
import Submission.Work.Gen.ChernGenerator

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `u² = c₁(O(1))²` generates `H⁴(ℂP⁴;ℤ)`

`Work.Gen.uSq 4` is the cup square of the hyperplane class `Work.Gen.uCoh 4 = c₁(O(1))` on `ℂP⁴`.
The same Gysin-sequence argument that computes `H²(ℂP⁴;ℤ)` in `Work.Gen.ChernGenerator`
(`H² = ℤ⟨u⟩`) computes `H⁴(ℂP⁴;ℤ)` one degree higher: for the rank-`2` real bundle
`Z = realification (tautDual 4)`, the Gysin exact sequence

`H²(ℂP⁴) --∪e--> H⁴(ℂP⁴) --> H⁴(E∖0) --> H³(ℂP⁴)`

has vanishing target `H⁴(E∖0) = 0` (the punctured total space is homotopy equivalent to the
punctured model space `ℂ⁵∖0 ≃ S⁹`, whose `H⁴` vanishes), so `∪ e` is onto.  Since
`e = u = uCoh 4`, the image of the generator `u = uCoh 4` of `H²(ℂP⁴;ℤ)` — hence `u ⌣ u` —
generates `H⁴(ℂP⁴;ℤ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Gen

open Work.Projective Work.Cohomology

noncomputable section

/-! ## Vanishing of the cohomology of the punctured model space, in all degrees -/

/-- **`H^k(ℂ^{m+2}∖{0};ℤ) = 0`** off the degrees `0` and `2m+3`: the general-degree form of
`Work.Gen.ChernGen.puncturedComplexH2Zero`, obtained from the Mayer–Vietoris computation
`Work.Projective.cpnUV_cohomology_zero` through the homeomorphism `Work.Projective.cpnUV_homeo`
identifying `cpU (m+2) ∩ cpV (m+2)` with `ℂ^{m+2}∖0`. -/
theorem uSqGen_puncturedComplexHZero (m k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 2 * m + 3) :
    CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ k (TopCat.of {z : Fin (m + 2) → ℂ // z ≠ 0})) := by
  obtain ⟨e⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (Work.Projective.cpnUV_homeo (m + 2)).toHomotopyEquiv k
  have hz : CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCohomology ℤ k
        (TopCat.of ↥(Work.Projective.cpU (m + 2) ∩ Work.Projective.cpV (m + 2)))) :=
    Work.Projective.cpnUV_cohomology_zero (m + 1) k hk0 (by omega)
  exact CategoryTheory.Limits.IsZero.of_iso hz e.symm

/-- **`H^k` of the punctured total space of `realification (tautDual 4)` vanishes** off the degrees
`0` and `9`, since that space is the punctured model space `ℂ⁵∖0`
(`Work.Gen.ChernGen.tautDualPunctHomeo`), which is homotopy equivalent to `S⁹`. -/
theorem uSqGen_puncturedTautDual4HZero (k : ℕ) (hk0 : k ≠ 0) (hktop : k ≠ 9) :
    CategoryTheory.Limits.IsZero
      (Work.Thom.Coh ℤ k
        ↥(Work.Thom.zeroComplement (Work.Thom.realification (tautDual 4)))) := by
  obtain ⟨e⟩ := ChernGen.tautDualPunctHomeo 4
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e.toHomotopyEquiv k
  exact CategoryTheory.Limits.IsZero.of_iso (uSqGen_puncturedComplexHZero 3 k hk0 (by omega)) iso

/-! ## The Gysin sequence of `O(1)` -/

/-- The Thom class of the tautological dual line bundle `O(1)` over `ℂP⁴`; its Euler class is
`u = c₁(O(1)) = Work.Gen.uCoh 4` (`Work.Thom.chernClass_one_top`). -/
noncomputable def uSqGen_T : Work.Thom.ThomClass (Work.Thom.realification (tautDual 4)) 2 :=
  Work.Thom.thomClassRank 1 (Nat.succ_le_succ (Nat.zero_le 0)) (tautDual 4)

/-- **The Gysin map `∪u : H^k(ℂP⁴;ℤ) → H^{k+2}(ℂP⁴;ℤ)` is onto** whenever `H^{k+2}(E∖0) = 0`,
i.e. `k + 2 ∉ {0, 9}`.  The Gysin sequence `H^k --∪e--> H^{k+2} --> H^{k+2}(E∖0)` is exact
(`Work.Thom.gysin_exact_at_base`), so the range of `∪e` is the kernel of the restriction to `E∖0`,
which is everything when `H^{k+2}(E∖0)` is a subsingleton. -/
theorem uSqGen_gysin_surj (k : ℕ) (hk0 : k + 2 ≠ 0) (hk : k + 2 ≠ 9) :
    Function.Surjective (Work.Thom.gysinEuler uSqGen_T k) := by
  intro y
  have hvan := uSqGen_puncturedTautDual4HZero (k + 2) hk0 hk
  haveI : Subsingleton ↑(Work.Thom.Coh ℤ (k + 2)
      ↥(Work.Thom.zeroComplement (Work.Thom.realification (tautDual 4)))) :=
    ModuleCat.subsingleton_of_isZero hvan
  have hrange := Work.Thom.gysin_exact_at_base uSqGen_T k
  have : y ∈ Set.range ⇑(Work.Thom.gysinEuler uSqGen_T k) := by
    rw [hrange]
    exact Subsingleton.elim _ _
  exact this

/-! ## The generator statement -/

/-- A surjective `ℤ`-linear map sends a generator to a generator. -/
theorem uSqGen_span_map_eq_top_of_surjective {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) (x : M)
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span]; simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

/-- **`u² = c₁(O(1))²` generates `H⁴(ℂP⁴;ℤ)`.**  The Gysin map `∪ u : H² → H⁴` of the tautological
dual line bundle is onto (`uSqGen_gysin_surj 2`), and it carries the generator `uCoh 4` of
`H²(ℂP⁴;ℤ)` (`Work.Gen.ChernGenerator`) to `uSq 4`; a surjective `ℤ`-linear map sends generators to
generators. -/
theorem uSqGenerates : Submodule.span ℤ {Work.Gen.uSq 4} = ⊤ := by
  have he : Work.Thom.gysinEuler uSqGen_T 2 (Work.Gen.uCoh 4) = Work.Gen.uSq 4 := by
    rw [Work.Thom.gysinEuler_eq_cupEuler]
    rfl
  have hgen := uSqGen_span_map_eq_top_of_surjective (Work.Thom.gysinEuler uSqGen_T 2)
    (uSqGen_gysin_surj 2 (by norm_num) (by norm_num)) (Work.Gen.uCoh 4) ChernGenerator
  rwa [he] at hgen

end

end Work.Gen
