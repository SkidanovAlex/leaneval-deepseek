import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le
import Submission.Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

/-!
# `Work.ShafarevichKoch.iSup_inertia_le_fixingSubgroup` -- the easy half of inertia generation

The finite-level inertia-generation theorem of `README.md` §16.6/§16.7 states that for a finite
Galois extension `L/F` whose relative different is supported on a set `S` of rational primes, the
Galois group of `L` over the *maximal* unramified intermediate field `N` is the subgroup generated
by the inertia subgroups of the primes above `S`:

```lean
N.fixingSubgroup = ⨆ (P : {P : Ideal (𝓞 L) // P.IsPrime ∧ ∃ q ∈ S, P.LiesOver (span {q})}),
    Ideal.inertia (L ≃ₐ[F] L) P.1
```

This module proves the **easy inclusion** `⊇` (`iSup_inertia_le_fixingSubgroup`): every inertia
subgroup at a prime `P` lies in `Gal(L/N)`, because `N/F` is unramified, so the inertia of
`P ∩ 𝓞 N` is trivial and hence `I_P ≤ ker (restrictNormalHom ↥N) = N.fixingSubgroup`.

The proof is the obvious diagram, with three inputs all already in the workspace:

* `Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal`
  (`¬ Q ∣ 𝔡 ↔ Q.ramificationIdx = 1`) and `hN : 𝔡(N/F) = ⊤` give `ramificationIdx = 1`;
* `Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one` turns that
  into `I_Q = ⊥`;
* `Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le` gives
  `(I_P).map (restrictNormalHom ↥N) ≤ I_Q = ⊥`, i.e. `I_P ≤ N.fixingSubgroup`
  (`IntermediateField.restrictNormalHom_ker`).

The **hard inclusion** `⊆` is the statement that `fixedField (⨆ I_P)` is unramified over `F`; it
needs surjectivity of the inertia under restriction, `I_{P∩𝓞M} = (I_P).map (restrictNormalHom ↥M)`
(from `D_P ↠ D_{P∩𝓞M}`).  See `README.md` §16.8.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option autoImplicit false

noncomputable section

namespace Work.ShafarevichKoch

theorem iSup_inertia_le_fixingSubgroup {F L : Type} [Field F] [Field L] [Algebra F L]
    [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L] (S : Finset ℕ)
    (N : IntermediateField F L) [FiniteDimensional F ↥N] [IsGalois F ↥N] [NumberField ↥N]
    (hN : differentIdeal (NumberField.RingOfIntegers F)
      (NumberField.RingOfIntegers ↥N) = ⊤) :
    (⨆ (P : {P : Ideal (NumberField.RingOfIntegers L) // P.IsPrime ∧
        ∃ q ∈ S, P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ))}),
      Ideal.inertia (L ≃ₐ[F] L) P.1) ≤ N.fixingSubgroup := by
  refine iSup_le fun P => ?_
  intro σ hσ
  haveI hPprime : P.1.IsPrime := P.2.1
  -- the primes under `P.1`
  have hQprime : (P.1.under (NumberField.RingOfIntegers ↥N)).IsPrime :=
    Ideal.IsPrime.under (NumberField.RingOfIntegers ↥N) P.1
  haveI : (P.1.under (NumberField.RingOfIntegers ↥N)).IsPrime := hQprime
  haveI hPliesQ : P.1.LiesOver (P.1.under (NumberField.RingOfIntegers ↥N)) := Ideal.LiesOver.mk rfl
  haveI hPliesp : P.1.LiesOver (P.1.under (NumberField.RingOfIntegers F)) := Ideal.LiesOver.mk rfl
  haveI hQliesp : (P.1.under (NumberField.RingOfIntegers ↥N)).LiesOver
      (P.1.under (NumberField.RingOfIntegers F)) :=
    Ideal.LiesOver.mk (Ideal.under_under P.1)
  -- `N/F` unramified makes the inertia of `P.1.under (𝓞 ↥N)` trivial
  have hIbot : Ideal.inertia (↥N ≃ₐ[F] ↥N) (P.1.under (NumberField.RingOfIntegers ↥N)) = ⊥ := by
    refine (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (F := F) (K := ↥N) (P.1.under (NumberField.RingOfIntegers F))
      (P.1.under (NumberField.RingOfIntegers ↥N))).mpr ?_
    refine (Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := F) (K := ↥N) (P.1.under (NumberField.RingOfIntegers ↥N)) hQprime).mp ?_
    rw [hN]
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hle : (⊤ : Ideal (NumberField.RingOfIntegers ↥N)) ≤
        P.1.under (NumberField.RingOfIntegers ↥N) := by
      rw [hc]; exact Ideal.mul_le_left
    exact hQprime.ne_top (top_le_iff.mp hle)
  -- the Commons comparison of inertia under restriction
  have hmap : (Ideal.inertia (L ≃ₐ[F] L) P.1).map
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := ↥N)) ≤ ⊥ := by
    rw [← hIbot]
    exact Commons.NumberTheory.RamificationInertia.inertia_map_restrictNormalHom_le
      (F := F) (L := ↥N) (M := L) (P.1.under (NumberField.RingOfIntegers F))
      (P.1.under (NumberField.RingOfIntegers ↥N)) P.1
  have hσ1 : AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := ↥N) σ = 1 := by
    have hmem : AlgEquiv.restrictNormalHom (F := F) (K₁ := L) (E := ↥N) σ
        ∈ (⊥ : Subgroup (↥N ≃ₐ[F] ↥N)) := hmap ⟨σ, hσ, rfl⟩
    simpa using hmem
  rw [← IntermediateField.restrictNormalHom_ker (E := N)]
  exact MonoidHom.mem_ker.mpr hσ1

end Work.ShafarevichKoch
