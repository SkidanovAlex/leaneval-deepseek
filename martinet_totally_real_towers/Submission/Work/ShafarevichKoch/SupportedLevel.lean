import Mathlib
import Submission.Work.ShafarevichKoch.SupportedSubextensions
import Submission.Work.ShafarevichKoch.InertiaCount
import Submission.Work.ShafarevichKoch.kSupported_universal

/-!
# `Work.ShafarevichKoch.SupportedLevel` -- addressing a finite level of the tower `k_∅ ⊆ k_S`

The bookkeeping that lets `Work.ShafarevichKoch.InertiaCount` be applied at a finite Galois level
`L ⊆ k_S/F`: the unramified part of `L` is `N := (k_∅).comap (val L)`, and

* `isGalois_comap_kEmpty` -- `N/F` is Galois (it is `F`-isomorphic to the appropriate subfield
  of `k_∅`);
* `differentIdeal_comap_kEmpty_eq_top` -- `N/F` is unramified (its different is trivial);
* `subextension_le_kSupported_empty` -- every finite Galois `M ≤ k_∅` is unramified
  (subextensions of the maximal unramified pro-`2` extension are unramified);
* `le_kEmpty_of_le_kSupported_of_unramified` -- and conversely, a finite Galois unramified pro-`2`
  subextension of `k_S` lies in `k_∅`, so `N` is the *maximal* unramified subextension of `L`
  (the hypothesis `hmax` of `InertiaCount`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- The unramified part of a finite Galois level `L ⊆ k_S`, as an intermediate field of `L`. -/
def kEmptyOf (F : Type) [Field F] [NumberField F] {L : IntermediateField F (AlgebraicClosure F)}
    (hL : L ≤ kSupported F 2 (∅ : Finset ℕ)) : IntermediateField F ↥L :=
  (kSupported F 2 (∅ : Finset ℕ)).comap (IntermediateField.val L)

/-- **A finite Galois subextension of `k_∅` is unramified** (its different is trivial). -/
theorem differentIdeal_eq_top_of_finite_galois_le_kEmpty {F : Type} [Field F] [NumberField F]
    {M : IntermediateField F (AlgebraicClosure F)} [FiniteDimensional F M] [IsGalois F M]
    [NumberField ↥M] (hM : M ≤ kSupported F 2 (∅ : Finset ℕ)) :
    differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥M) = ⊤ := by
  classical
  obtain ⟨-, hsupp⟩ := kSupported_supp_and_pGroup (F := F) (p := 2) (∅ : Finset ℕ) hM
  refine Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_forall_not_dvd
    (E := F) (K := ↥M) ?_
  intro Q hQ
  by_cases hQbot : Q = ⊥
  · rw [hQbot]
    intro h
    obtain ⟨c, hc⟩ := h
    have hbot : differentIdeal (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥M)
        = ⊥ := by
      rw [hc]; simp
    exact differentIdeal_ne_bot hbot
  · intro hdvd
    obtain ⟨q, hq, -⟩ := hsupp Q hQ hQbot hdvd
    simp at hq

end Work.ShafarevichKoch
