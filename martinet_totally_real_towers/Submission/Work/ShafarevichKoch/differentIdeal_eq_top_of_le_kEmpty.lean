import Mathlib
import Submission.Work.ShafarevichKoch.SupportedLevel
import Submission.Work.ShafarevichKoch.SupportedComparison
import Submission.Work.ShafarevichKoch.SupportedSubextensions
import Submission.Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv

set_option linter.style.haveILetI false

namespace Work.ShafarevichKoch

/-- **A finite Galois subextension of `k_S` which lies in the image of `k_∅` is unramified.**

If `M ≤ kEmptyInS F p S` -- i.e. `M` is contained in the image inside `k_S` of the maximal
everywhere-unramified pro-`p` extension `k_∅` -- then `M/F` is unramified at every finite prime,
equivalently `differentIdeal (𝓞 F) (𝓞 ↥M) = ⊤`.

The proof transports along the `F`-algebra isomorphism `↥M ≃ₐ[F] ↥(M.lift)`
(`IntermediateField.liftAlgEquiv`): the lift of `M` into the algebraic closure is contained in
`k_∅` (membership in `kEmptyInS` is exactly membership of the underlying element in `k_∅`), so the
already proved `differentIdeal_eq_top_of_finite_galois_le_kEmpty` applies to it, and the triviality
of the different is invariant under `F`-algebra isomorphisms
(`Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv`). -/
theorem differentIdeal_eq_top_of_le_kEmpty {F : Type} [Field F] [NumberField F] (S : Finset ℕ) (M : IntermediateField F ↥(Work.ShafarevichKoch.kSupported F 2 S)) [FiniteDimensional F ↥M] [IsGalois F ↥M] [NumberField ↥M] (hM : M ≤ Work.ShafarevichKoch.kEmptyInS F 2 S) : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥M) = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the `F`-algebra isomorphism between `M` and its lift to the algebraic closure
  let e : ↥M ≃ₐ[F] ↥(IntermediateField.lift M) := IntermediateField.liftAlgEquiv M
  haveI hfdLift : FiniteDimensional F ↥(IntermediateField.lift M) := e.toLinearEquiv.finiteDimensional
  haveI hgalLift : IsGalois F ↥(IntermediateField.lift M) := IsGalois.of_algEquiv e
  haveI hnumLift : NumberField ↥(IntermediateField.lift M) :=
    NumberField.of_module_finite F ↥(IntermediateField.lift M)
  -- the lift of `M` is contained in `k_∅`
  have hlift : IntermediateField.lift M ≤ kSupported F 2 (∅ : Finset ℕ) := by
    intro x hx
    have hxK : x ∈ kSupported F 2 S := IntermediateField.lift_le M hx
    let y : ↥(kSupported F 2 S) := ⟨x, hxK⟩
    have hyM : y ∈ M := (IntermediateField.mem_lift y).mp hx
    have hy : y ∈ kEmptyInS F 2 S := hM hyM
    exact hy
  have htop : differentIdeal (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers ↥(IntermediateField.lift M)) = ⊤ :=
    differentIdeal_eq_top_of_finite_galois_le_kEmpty (F := F)
      (M := IntermediateField.lift M) hlift
  exact Work.ClassFieldTower.differentIdeal_eq_top_of_algEquiv e.symm htop

end Work.ShafarevichKoch
