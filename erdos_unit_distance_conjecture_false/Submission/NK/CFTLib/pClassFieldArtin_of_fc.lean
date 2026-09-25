import Mathlib
import Submission.CFTLib.Interfaces
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.CFTLib.ClassChar
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely_of_le
import Submission.NK.CFTLib.Existence.classField_exists_primeIndex
import Submission.NK.CFTLib.Existence.splitting_of_normClass
import Submission.NK.CFTLib.ArtinReciprocityIdealProved

/-!
# The `p`-class field of a character, in Artin form, from the fundamental class

Target (`NK.CFTLib.pClassFieldArtin_of_fc`, the statement below): from the existence of the
global fundamental class `hFC : NK.GlobalCFTdeep.FundamentalClassElement`, deduce

`CFTLib.PClassFieldArtin` : for `χ : Cl(K) →* Multiplicative (ZMod p)` nontrivial, there is a
cyclic degree-`p` extension `L / K`, unramified at every place, in which a finite prime `v` splits
completely (`Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1`) if and only if `χ [v] = 1`.

## What this file contains

* `NK.CFTLib.normClassSubgroup_mem_of_inertiaDegIn_eq_one` — the **provable half** of the
  splitting law for an unramified abelian extension: a prime whose inertia degree is `1` (hence,
  unramified, a completely split prime) has its idèle in the norm class subgroup.  This is proved
  from `NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely` and
  the Mathlib identity `ncard * (e * f) = |Gal(L/K)|`.
* `NK.CFTLib.pClassFieldArtin_of_inputs` — the **assembly**: `PClassFieldArtin` follows from
  `hFC` together with exactly two classical inputs (recorded as explicit hypotheses):
  * `hEx` — the *existence theorem* in the index-`p` case: every open finite-index subgroup
    `V ≤ C_K` of index `p` containing the image of the integral idèles is the norm class subgroup
    of an unramified degree-`p` extension (Hilbert–Furtwängler / Takagi);
  * `hSplit` — the *other* half of the splitting law: the class of the idèle of a prime lying in
    the norm class subgroup forces the prime to split completely (Kronecker's splitting law, i.e.
    the prime–Frobenius compatibility of the Artin map).

## Status of the target

The target is **wired**: it is proved from the two lemmas on the frontier of the `CFTLib` chain

* `NK.CFTLib.Existence.classField_exists_primeIndex` (the existence theorem of the two inputs
  above, at a modulus, from the ideal-theoretic reciprocity law), and
* `NK.CFTLib.Existence.splitting_of_normClass` (the splitting law of the two inputs above),
  each applied to the ideal-theoretic reciprocity law
  `NK.CFTLib.artinReciprocityIdeal : NK.CFTLib.ArtinReciprocityIdeal`
  (`Submission/Work/CFTLib/artinReciprocityIdeal.lean`, whose remaining obligation — Lang X.2
  Theorem 2, the cyclic case — is `NK.CFTLib.ArtinReciprocityIdeal.kernelLeOfAdmissible`; see
  `Submission/Work/CFTLib/ArtinReciprocityIdeal/NOTES.md`).

The wiring below uses the **proved, axiom-clean** reciprocity law
`NK.CFTLib.artinReciprocityIdeal_proved` (`Submission/Work/CFTLib/ArtinReciprocityIdealProved.lean`),
so the only work in this file beyond the assembly is the *provable* half of the splitting law
(`normClassSubgroup_mem_of_inertiaDegIn_eq_one`).

Current status of the two frontier lemmas:

* `NK.CFTLib.Existence.splitting_of_normClass` is axiom-clean;
* `NK.CFTLib.Existence.classField_exists_primeIndex` (to which this file's `hEx` is wired) still
  inherits `sorryAx`, from exactly two open files in its closure:
  `Submission/Work/CFTLib/hilbertReciprocity_cyclic.lean` (the unwired form of the
  one-place Hilbert reciprocity `HilbertReciprocityOnePlace`) and
  `Submission/Work/CFTLib/Existence/localNormImage_of_forall_ne.lean`.
  The designated port `NK.CFTLib.HR.hilbertReciprocityOnePlace_proof` is in place but is itself
  still `sorryAx`-tainted through its own closure, so it cannot yet be used to discharge them.
As soon as those become axiom-clean, this file does too, with no further edit.

The *idèle-level* form of the splitting law, by contrast, is elementary and is proved in this
workspace (`NK.CFTLib.Splitting.inertiaDegIn_eq_one_iff_mem_normImage`): the whole content of
`hSplit` is the passage from the class-level membership `mk K (ideleOfPrime K v) ∈ N_{L/K}C_L` to
the idèle-level one (the "principal correction" `x = a · N(y)` with `a ∈ K^×`).

The *idèle-level* splitting law, on the other hand, is elementary and has been proved in this
workspace:
`NK.CFTLib.Splitting.inertiaDegIn_eq_one_iff_mem_normImage`
(`Submission/Work/CFTLib/Splitting/inertiaDegIn_eq_one_iff_mem_normImage.lean`), namely
`Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1 ↔ ideleOfPrime K v ∈ Idele.normImage K L` for an
unramified extension.  The whole arithmetic content of the missing half is therefore the passage
from the class-level membership `mk K (ideleOfPrime K v) ∈ N_{L/K}C_L` to the idèle-level one
(the "principal correction" `x = a · N(y)` with `a ∈ K^×`), which is exactly the prime–Frobenius
compatibility.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

/-! ## The provable half of the splitting law -/

/-- **A completely split prime is a norm.**  Let `L / K` be a finite Galois extension of number
fields which is unramified at every finite place (`differentIdeal = ⊤`) and let `v` be a finite
prime of `K` of inertia degree `1` in `L`.  Then the idèle of `v` (the chosen uniformiser at `v`
and `1` everywhere else) is a norm from `L`, hence its class lies in the norm class subgroup
`N_{L/K} C_L`.

Since `differentIdeal = ⊤` gives `e = 1`, the hypothesis `Ideal.inertiaDegIn v (𝓞 L) = 1` says
that `v` splits completely, and the result is the sharper formulation
`NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely`. -/
theorem normClassSubgroup_mem_of_inertiaDegIn_eq_one
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hfin : differentIdeal (𝓞 K) (𝓞 L) = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (hv : Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1) :
    IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K v) ∈ Idele.normClassSubgroup K L := by
  classical
  letI : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  -- the ramification index of `v` in `L` is `1`, since `L/K` is unramified at every finite place
  obtain ⟨Q, hQ⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := K) (L := L) v
  haveI : Q.asIdeal.LiesOver v.asIdeal := hQ
  have he : v.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q.asIdeal (L ≃ₐ[K] L)]
    exact ramificationIdx_eq_one_of_differentIdeal_eq_top (K := K) (L := L) hfin Q
  -- hence `v` splits completely: the number of primes over `v` is `[L : K]`
  have hcard : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have hncard : (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by
    have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      v.asIdeal (𝓞 L) (L ≃ₐ[K] L)
    rw [he, hv, mul_one, mul_one, hcard] at h
    exact h
  -- the idèle of a completely split prime is a norm
  have hmem : NK.HeckeL.ideleOfPrime K v ∈ Idele.normImage K L :=
    NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely
      (K := K) (L := L) v hncard
  rw [show Idele.normClassSubgroup K L = (Idele.normImage K L).map (IdeleClassGroup.mk K) from rfl]
  exact Subgroup.mem_map.mpr ⟨NK.HeckeL.ideleOfPrime K v, hmem, rfl⟩

/-! ## The assembly -/

/-- **The `p`-class field of a character, in Artin form, from the fundamental class, the existence
theorem and the splitting law.**

This is the reduction of the target to the two classical inputs displayed in the statement; both
are hypotheses here, and the only named input used is the fundamental class `hFC`
(via `NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement`, i.e. the reciprocity
isomorphism `C_K ⧸ N_{L/K}C_L ≅ Gal(L/K)` for the abelian extension `L/K` produced by `hEx`).

For `χ ≠ 1` take the open finite-index subgroup `V := ker(classChar K p χ) ≤ C_K` of index `p`,
which contains the image of the integral idèles; `hEx` produces an unramified degree-`p` extension
`L/K` with `N_{L/K}C_L = V`.  The two directions of the equivalence are then
`χ [v] = 1 ⟺ mk (ideleOfPrime K v) ∈ N_{L/K}C_L` (by definition of `V`, `classChar` and
`idealClassHom_mk_ideleOfPrime`), and `mk (ideleOfPrime K v) ∈ N_{L/K}C_L ⟺ v` splits completely
(`hSplit` and `normClassSubgroup_mem_of_inertiaDegIn_eq_one`). -/
theorem pClassFieldArtin_of_inputs
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hEx : ∀ {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
      (V : Subgroup (IdeleClassGroup K)), V.FiniteIndex →
      IsOpen (V : Set (IdeleClassGroup K)) → V.index = p →
      (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ V →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
        IsGalois K L ∧ Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p ∧
        differentIdeal (𝓞 K) (𝓞 L) = ⊤ ∧ IsUnramifiedAtInfinitePlaces K L)
    (hSplit : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
      (hunr : differentIdeal (𝓞 K) (𝓞 L) = ⊤),
      ∀ v : HeightOneSpectrum (𝓞 K),
        IdeleClassGroup.mk K (NK.HeckeL.ideleOfPrime K v) ∈ Idele.normClassSubgroup K L →
        Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1) :
    CFTLib.PClassFieldArtin := by
  intro K _ _ p _ χ hχ
  let V : Subgroup (IdeleClassGroup K) := (classChar K p χ).ker
  have hidx : V.index = p := index_ker_classChar K p χ hχ
  have hfin : V.FiniteIndex := by
    refine Subgroup.finiteIndex_iff.mpr ?_
    rw [hidx]
    exact (Fact.out (p := p.Prime)).ne_zero
  have hint : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ V :=
    integralIdeles_map_le_ker_classChar K p χ
  have hopen : IsOpen (V : Set (IdeleClassGroup K)) :=
    isOpen_of_le_isOpen (isOpen_map_integralIdeles K) hint
  obtain ⟨L, hF, hN, hA, hfd, hGal, hnorm, hdeg, hdiff, hinf⟩ :=
    hEx (K := K) p V hfin hopen hidx hint
  -- the norm class subgroup is a kernel of a character, so the Artin map is abelian:
  haveI : IsMulCommutative (L ≃ₐ[K] L) := by
    haveI : IsCyclic (L ≃ₐ[K] L) :=
      isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank K L, hdeg])
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
    obtain ⟨k, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hg a)
    obtain ⟨l, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hg b)
    exact Commute.zpow_zpow_self g k l
  refine ⟨L, hF, hN, hA, hfd, hGal, hdeg, ⟨hdiff, hinf⟩, fun v => ⟨?_, ?_⟩⟩
  · -- `v` splits completely `⟹ χ [v] = 1`
    intro hv
    have hmem := normClassSubgroup_mem_of_inertiaDegIn_eq_one (K := K) (L := L) hdiff v hv
    rw [hnorm, MonoidHom.mem_ker, classChar_apply, idealClassHom_mk_ideleOfPrime K v] at hmem
    exact hmem
  · -- `χ [v] = 1 ⟹ v` splits completely
    intro hv
    refine hSplit (K := K) (L := L) hdiff v ?_
    rw [hnorm, MonoidHom.mem_ker, classChar_apply, idealClassHom_mk_ideleOfPrime K v]
    exact hv

/-! ## The target -/

/-- **The `p`-class field of a character, in Artin form, from the fundamental class.**

The final wiring of `pClassFieldArtin_of_inputs` to the frontier lemmas: the existence theorem
`NK.CFTLib.Existence.classField_exists_primeIndex`, applied to `hFC` and to the ideal-theoretic
reciprocity law `NK.CFTLib.artinReciprocityIdeal`, supplies `hEx`, and
`NK.CFTLib.Existence.splitting_of_normClass` supplies `hSplit`.  The two frontier lemmas are
stated in exactly the form of the two hypotheses of `pClassFieldArtin_of_inputs` (compare the
signatures), so no argument massaging is needed. -/
theorem pClassFieldArtin_of_fc (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    CFTLib.PClassFieldArtin :=
  pClassFieldArtin_of_inputs hFC
    (NK.CFTLib.Existence.classField_exists_primeIndex
      NK.CFTLib.artinReciprocityIdeal_proved hFC)
    (NK.CFTLib.Existence.splitting_of_normClass NK.CFTLib.artinReciprocityIdeal_proved)

end NK.CFTLib
