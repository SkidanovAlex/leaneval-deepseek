import Mathlib
import Submission.Work.BG.CliffordLib
import Submission.Work.BG.conjByEqSelfOfSupZpowersEqTop

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **Conjugation by the co-covering element swaps the two constituents.**

Let `N ⊴ X` be a finite normal subgroup, `y ∈ X` an element whose powers together with `N`
cover `X` (`X = N · ⟨y⟩`), and let `ν` be an irreducible character of `X` whose restriction
to `N` is the sum of two *distinct* irreducible characters `A` and `A₂` of `N`.  Then `y`
does not fix `A`: `A^y ≠ A`.

The reason is Clifford's single-orbit theorem.  If `A^y = A`, then `A^x = A` for every
`x ∈ X` (write `x = n y^k`: conjugation by `n ∈ N` fixes every class function of `N`, and
conjugation by `y^k` fixes `A` by hypothesis), so the `X`-conjugation orbit of `A` is the
singleton `{A}`.  But the constituents `A`, `A₂` of `Res_N ν` all lie in a single
`X`-conjugation orbit (`restrictionConstituentsSingleOrbit_of_isIrreducible`), forcing
`A₂ = A`, contrary to hypothesis. -/
theorem ConjByTwoConstituents {X : Type} [Group X]
    (N : Subgroup X) [N.Normal] [Fintype ↥N] [Invertible (Nat.card ↥N : ℂ)]
    {ν : OddOrder.RepresentationTheory.ClassFunction X ℂ}
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν)
    {A A₂ : OddOrder.RepresentationTheory.ClassFunction ↥N ℂ}
    (hA : OddOrder.RepresentationTheory.IsIrreducibleCharacter A)
    (hA₂ : OddOrder.RepresentationTheory.IsIrreducibleCharacter A₂) (hne : A₂ ≠ A)
    (hres : OddOrder.RepresentationTheory.ClassFunction.restrict N ν = A + A₂)
    {y : X} (hcov : ∀ x : X, ∃ n ∈ N, ∃ k : ℤ, x = n * y ^ k) :
    OddOrder.RepresentationTheory.ClassFunction.conjBy (G := X) (H := N) y A ≠ A := by
  classical
  intro hfix
  -- ### Step 1: `X = N · ⟨y⟩`, so `A^y = A` forces `A` to be `X`-invariant.
  have htop : N ⊔ Subgroup.zpowers y = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨n, hn, k, rfl⟩ := hcov x
    exact Subgroup.mul_mem_sup hn (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
  have hAll : ∀ g : X, ClassFunction.conjBy (G := X) (H := N) g A = A :=
    conjByEqSelfOfSupZpowersEqTop N y htop A hfix
  -- ### Step 2: `A` and `A₂` are constituents of `Res_N ν`.
  let χ : IrreducibleCharacter X := ⟨ν, hν⟩
  let Ā : IrreducibleCharacter ↥N := ⟨A, hA⟩
  let Ā₂ : IrreducibleCharacter ↥N := ⟨A₂, hA₂⟩
  have hne' : Ā₂ ≠ Ā := fun h =>
    hne (congrArg (fun η : IrreducibleCharacter ↥N => (η : ClassFunction ↥N ℂ)) h)
  have hres' : ClassFunction.restrict N (χ : ClassFunction X ℂ) =
      (Ā : ClassFunction ↥N ℂ) + (Ā₂ : ClassFunction ↥N ℂ) := by
    simpa [χ, Ā, Ā₂] using hres
  have hselfA : ClassFunction.inner (Ā : ClassFunction ↥N ℂ) (Ā : ClassFunction ↥N ℂ) = 1 := by
    rw [irreducibleCharacter_inner_eq_ite]
    simp
  have hselfA₂ : ClassFunction.inner (Ā₂ : ClassFunction ↥N ℂ) (Ā₂ : ClassFunction ↥N ℂ) = 1 := by
    rw [irreducibleCharacter_inner_eq_ite]
    simp
  have horth₂ : ClassFunction.inner (Ā₂ : ClassFunction ↥N ℂ) (Ā : ClassFunction ↥N ℂ) = 0 := by
    rw [irreducibleCharacter_inner_eq_ite]
    rw [ite_eq_right hne']
  have horth : ClassFunction.inner (Ā : ClassFunction ↥N ℂ) (Ā₂ : ClassFunction ↥N ℂ) = 0 := by
    rw [irreducibleCharacter_inner_eq_ite]
    rw [ite_eq_right (Ne.symm hne')]
  have hliesA : IrreducibleCharacter.LiesOver N χ Ā := by
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def, hres',
      ClassFunction.inner_add_left, hselfA, horth₂, add_zero]
    exact one_ne_zero
  have hliesA₂ : IrreducibleCharacter.LiesOver N χ Ā₂ := by
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def, hres',
      ClassFunction.inner_add_left, horth, hselfA₂, zero_add]
    exact one_ne_zero
  -- ### Step 3: Clifford's single-orbit theorem forces `A₂ = A`.
  obtain ⟨x, hx⟩ :=
    (restrictionConstituentsSingleOrbit_of_isIrreducible (H := N) χ).exists_conj hliesA hliesA₂
  have hxA : ClassFunction.conjBy (G := X) (H := N) x A = A₂ := by
    have h := congrArg (fun η : IrreducibleCharacter ↥N => (η : ClassFunction ↥N ℂ)) hx
    simpa [Ā, Ā₂, IrreducibleCharacter.coe_conjBy] using h
  rw [hAll x] at hxA
  exact hne hxA.symm

end Work.BG
