import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup

/-!
# `Work.ShafarevichKoch.SupportedInfUnramified` -- `L ⊓ k_∅` is the maximal unramified part of `L`

For a finite Galois pro-`p` `S`-supported level `L = i.L` (`Submission.NumberField.SupportedPField
F p S`), every finite Galois subextension `K ≤ i.L` which is unramified over `F` (trivial relative
different) is contained in `i.L ⊓ kSupported F p ∅`.  Equivalently: **`i.L ⊓ k_∅` is the maximal
(hence, by `k_∅`'s definition, the *only*) unramified Galois subextension of `i.L` up to itself**,
which is the `hmax` hypothesis of the finite-level inertia-generation theorem
`Work.ShafarevichKoch.fixingSubgroup_eq_iSup_inertia` (README §16.6, item (ii)).

The proof is a three-line use of the two defining properties of the chapter's tower:

* `K ≤ i.L` and `i.L/F` finite Galois pro-`p` ⟹ `K/F` is pro-`p`
  (`Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup`, applied to the
  one-element family `fun _ : Unit => i.L`);
* `differentIdeal = ⊤` makes the `S = ∅` support condition vacuous, so `K` is a
  `SupportedPField F p ∅`, hence `K ≤ k_∅` by `le_kSupported`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **An unramified Galois subextension of an `S`-supported pro-`p` level lies in `L ⊓ k_∅`.** -/
theorem inf_kSupported_le_of_unramified {F : Type} [Field F] [NumberField F] {p : ℕ}
    [Fact p.Prime] {S : Finset ℕ} (i : Submission.NumberField.SupportedPField F p S)
    {K : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F K] [IsGalois F K]
    [NumberField ↥K] (hK : K ≤ i.L)
    (hunr : differentIdeal (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers ↥K) = ⊤) :
    K ≤ i.L ⊓ kSupported F p (∅ : Finset ℕ) := by
  refine le_inf hK (le_kSupported (F := F) (p := p) (S := (∅ : Finset ℕ))
    { L := K, hpg := ?_, hsupp := ?_ })
  · exact Commons.FieldTheory.Galois.isPGroup_aut_of_le_iSup_finite_galois_pGroup
      (F := F) (K := AlgebraicClosure F) (p := p) (f := fun _ : Unit => i.L)
      (fun _ => i.hfd) (fun _ => i.hgal) (fun _ => i.hpg)
      (by simpa using hK)
  · intro P hP hPne hPdvd
    rw [hunr] at hPdvd
    obtain ⟨c, hc⟩ := hPdvd
    have hle : (⊤ : Ideal (NumberField.RingOfIntegers ↥K)) ≤ P := by
      rw [hc]; exact Ideal.mul_le_left
    exact absurd (top_le_iff.mp hle) hP.ne_top

end Work.ShafarevichKoch
