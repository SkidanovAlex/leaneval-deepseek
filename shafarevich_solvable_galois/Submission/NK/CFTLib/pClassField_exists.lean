import Mathlib
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely
import Submission.NK.GlobalCFTdeep.SecondInequality.primeClass_eq_one_of_splitsCompletely_of_le

import Submission.NK.CFTLib.integralIdelesLeNormImage
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.CFTLib.ClassChar
import Submission.CFTLib.Interfaces
import Submission.NK.CFTLib.Existence.classField_exists_primeIndex
import Submission.NK.CFTLib.Existence.splitting_of_normClass
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.CFTLib.fundamentalClassElement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `p`-class field with prescribed splitting: the reduction

Let `K` be a number field, `p` a prime, `T` a finite set of finite primes of `K` and
`χ : Cl(K) →* Multiplicative (ZMod p)` a nontrivial character of the ideal class group of `K`
which kills the classes of the primes in `T`.  The theorem to be proved
(`NK.CFTLib.pClassField_exists`) is the existence of a finite Galois extension `L / K` of
degree `p` which is unramified at every prime (finite: `differentIdeal = ⊤`; infinite: real
places stay real) and in which every prime of `T` has inertia degree `1`.

This file implements the **reduction** of that statement to two classical inputs, both of which
are (Furtwängler's theorem / Artin's reciprocity law):

* `existenceTheoremIndexPrime` — every index-`p` subgroup of the idèle class group `C_K` which
  contains the image of the modulus-1 ray group `Idele.integralIdeles K` (the idèles that are
  local units at every finite place) is the norm group `N_{L/K} C_L` of an unramified
  degree-`p` extension `L / K` (delegated as
  `NK.CFTLib.Existence.normClassSubgroup_eq_of_index_prime`);
* `splittingLaw` — for an abelian extension `L / K` unramified at a prime `𝔭`, the class of the
  idèle of `𝔭` lies in the norm group iff `𝔭` splits completely (delegated as
  `NK.CFTLib.Splitting.inertiaDeg_eq_one_of_mem_normClassSubgroup`).

The bridge is the ideal class map: `IdeleClassGroup.idealClassHom K : C_K →* Cl(K)` is
surjective (`GlobalCFT_idealClassMap_exists`) with kernel the image of `Idele.integralIdeles K`,
so a character `χ` of `Cl(K)` pulls back to a character `χ̃ = classChar K p χ` of `C_K` whose
kernel `V` has index `p` (because `χ ≠ 1` and `Multiplicative (ZMod p)` has order the prime `p`),
contains the modulus-1 ray group, and contains the class of the idèle of every prime in `T`
(by the hypothesis on `χ`).
-/

/-!
## Route to the target (session notes, keep)

The target `pClassField_exists` is reduced by `exists_pClassField_of_inputs` to two classical
inputs.  The route now being pursued replaces both by *analytic-free* arguments:

1. **The norm-kernel principle** (`normClassSubgroup_eq_top_of_unramified_of_generating_splits`
   below, proved): an everywhere unramified finite abelian extension of `K` in which the primes of
   a class-group-generating set split completely is trivial.  Only the two *easy* directions of
   class field theory are used (a completely split prime has its prime idèle in the norm group,
   `NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely`; an
   unramified extension contains the modulus-one ray group,
   `NK.CFTLib.integralIdelesLeNormImage`), together with the index formula
   `[C_K : N_{L/K}C_L] = [L:K]` for **cyclic** `L/K`
   (`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`, unconditional).  This is Milne, *CFT*,
   Proposition 9.2, which he deduces from the reciprocity law.

2. **Existence of the class field of `V`.**  Take a finite set `S` of places containing the places
   above `p`, with `⊤ = Kˣ · 𝕀_{K,S}` (weak approximation, `top_eq_principal_sup_TIdeles`), and put
   `L_S = K(U(S)^{1/p})`, whose Galois group is `(Z/p)^{|S|}`.  The map
   `Δ ↦ N_{K(Δ^{1/p})/K}` from subgroups `Δ ≤ U(S)/U(S)^p` to subgroups of `C_K` is a bijection
   from the maximal subgroups of `U(S)/U(S)^p` onto the index-`p` subgroups `V'` with
   `N_{L_S} ≤ V' ≤ C_K`:
   * injectivity: `N_{M_1} = N_{M_2}` forces `[M_1M_2 : K] = [M_1 : K]` using the *abelian* index
     formula (a missing library lemma, `NK.CFTLib.Existence.index_eq_finrank_of_isAbelian`);
   * cardinalities: `[C_K : N_{L_S}] = [L_S : K] = p^{|S|}` (abelian index formula + Kummer degree)
     and `#U(S)/U(S)^p = p^{|S|}` (Dirichlet).
   Since the index-`p` subgroups `V` with `V ⊇ R := im(∏_v O_vˣ)` are exactly the `V` containing
   `KˣE_S/K^×` — this is the Milne 9.3 computation `N_{L_S} = KˣE_S/K^×`, where
   `E_S = ∏_{v∈S}K_v^{×p}·∏_{v∉S}U_v`, and its inclusion in `V` uses `V ⊇ C_K^p` and `V ⊇ R` — the
   target's `V = ker χ̃` is in the image, giving `L = K(Δ^{1/p})` with `N_L = V`, cyclic of degree
   `p`.

3. **Unramifiedness and the splitting of `T`.**  For `v ∤ p` unramifiedness is immediate from the
   Kummer criterion for local units (`kummerField_ramificationIdx_eq_one_of_unit`).  For the
   remaining places `v | p`, and for the primes of `T`, the same *counting* structure is used:
   the local condition on `Δ` (a local `p`-th power / the unramified local class at `v`) cuts out
   a subgroup whose index can be compared with the number of index-`p` subgroups of `C_K/N_{L_S}`
   containing the idèle of `v`; because the bijection above matches the two lattices, the *global*
   condition `x_v ∈ V` (which holds for `v ∈ T` by the hypothesis `hT`) implies the *local*
   condition, hence splitting.  The numerical input needed is that the image of `U(S)/U(S)^p` in
   `K_v^×/K_v^{×p}` has order `≤ p` for `v ∤ p` (immediate from `O_v^×/(O_v^×)^p ≅ κ_v^×/(κ_v^×)^p`).

**Status of the missing arithmetic input (reviewed twice, 2 independent reviewers agree).**  The
*only* arithmetic input the target still needs is the **prime–Frobenius compatibility of the Artin
map at unramified primes** (Milne, *CFT*, V.5.3(a); equivalently Hilbert's reciprocity law
`∑_v inv_v = 0`): for an abelian `L/K`, an unramified prime `𝔭`, and `x_𝔭 = ideleOfPrime K 𝔭`,

  `mk K x_𝔭 ∈ N_{L/K}C_L  ⟹  𝔭` splits completely in `L`.

It is available in the workspace only as a *named, unproved structure field*:
`NK.HeckeL.FrobeniusCompatibility.iso_primeClass` (file `Submission/Work/HeckeL/Dictionary.lean`)
and `NK.Chebotarev.ArtinReciprocityInput`.  In particular the global fundamental class
`NK.GlobalCFTdeep.FundamentalClassElement` does **not** suffice: it yields only a *bare*
isomorphism `C_K ⧸ N_{L/K}C_L ≃* Gal(L/K)`, which can be twisted by any automorphism of
`Gal(L/K)` and therefore carries no information about *which* element is the image of a given
prime.  This is recorded in `Submission/Work/CFTLib/pClassFieldArtin_of_fc.lean`.  Consequently the
counting argument of point 3 above (whose injectivity step is "a cyclic degree-`p` extension is
determined by its norm group") cannot be completed unconditionally either: a child proved and
committed the two numerical halves it needs
(`NK.CFTLib.Existence.index_kummerE_sup_principal`: `[C_K : KˣE_S/K^×] = p^{|S|}`;
`NK.CFTLib.Existence.kummerE_le_normImage_of_kummerField`: `E_S ≤ N 𝕀`), but the injectivity
estep needs the same prime–Frobenius compatibility.

**Proved (child, on disk, sorry-free):**
`NK.CFTLib.Splitting.inertiaDeg_eq_one_of_frobeniusCompatibility`
(`Submission/Work/CFTLib/Splitting/inertiaDeg_eq_one_of_frobeniusCompatibility.lean`) — the input
`hSplit` of `exists_pClassField_of_inputs` follows from `NK.HeckeL.FrobeniusCompatibility`
(Milne V.5.3(a)) together with the naturality hypothesis
`N_{L/K}C_L ≤ ker (rayClassGroupMk K U)`; this discharges the *splitting* half of the target
modulo the licensed input.  Also proved: `NK.CFTLib.Splitting.inertiaDeg_eq_one_of_mem_normImage`
(the elementary half), `NK.CFTLib.Existence.index_kummerE_sup_principal` and
`NK.CFTLib.Existence.kummerE_le_normImage_of_kummerField` (the Milne 9.3 numerical halves).

**New (a child's result, on disk):** the *elementary half* of the splitting law is proved:
`NK.CFTLib.Splitting.inertiaDeg_eq_one_of_mem_normImage` (file
`Submission/Work/CFTLib/Splitting/inertiaDeg_eq_one_of_mem_normImage.lean`) shows, for an arbitrary
finite Galois `L/K` and a prime `𝔭`, that `ideleOfPrime K 𝔭 ∈ Idele.normImage K L` implies that `𝔭`
splits completely in `L` — the valuation of a local norm is `f` times an integer, while
`ideleOfPrime` has valuation `±1`, so `f ∣ 1`.  What is *not* available is the upgrade from the
class-level membership `mk K (ideleOfPrime K 𝔭) ∈ N_{L/K}C_L` to `ideleOfPrime K 𝔭 ∈ N 𝕀_L`
(equivalently: "no single place of local-norm failure", i.e. Hilbert reciprocity / the canonical
Frobenius property of the Artin isomorphism); the counting structure of point 3 above is the
substitute for it and is the route being pursued.

The pieces still missing from the library are therefore:
* `NK.CFTLib.Existence.index_eq_finrank_of_isAbelian` — the index formula `[C_K : N_{L/K}C_L] =
  [L:K]` for abelian `L/K` (multiplicativity of the Herbrand quotient, reducing to the cyclic
  case);
* the Milne 9.3 computation `N_{K(U(S)^{1/p})} = KˣE_S/K^×` (index count
  `[𝕀_K : Kˣ·E_S] = p^{|S|}` out of the local count `∏_{v∈S}(K_vˣ : K_v^{×p}) = p^{2|S|}`,
  available as `KummerCase.prod_localPow_eq_pow`, and Dirichlet);
* the counting/splitting argument of point 3.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct IsMulCommutative nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT


/-! ## The norm-kernel principle

The following two lemmas are the reciprocity-free half of the conductor–norm-group dictionary for
an unramified extension: an (abelian, indeed cyclic) extension which is unramified at every finite
place is *trivial* as soon as the primes of a set generating the ideal class group of `K` split
completely in it.

The proof only uses the two easy directions of class field theory, both available unconditionally
in this workspace: a prime which splits completely has its prime idèle in the norm group
(`NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely`), and an
unramified extension has the modulus-one ray group (the image of the integral idèles) inside its
norm group (`NK.CFTLib.integralIdelesLeNormImage`).  Consequently the norm group of such an
extension contains the kernel of the ideal class map `C_K →* Cl(K)` and maps onto `Cl(K)`, hence is
all of `C_K`; the index formula `[C_K : N_{L/K}C_L] = [L : K]` for cyclic `L/K`
(`NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`) then forces `L = K`.

This is Milne, *Class Field Theory*, Proposition 9.2, which he deduces from the reciprocity law; the
argument above avoids it, and is used below to compute the norm group of the Kummer extension
`K(U(S)^{1/p})`. -/

/-- **The norm-kernel principle**: an everywhere unramified cyclic extension in which the primes of
a class-group-generating set split completely is trivial. -/
theorem normClassSubgroup_eq_top_of_unramified_of_generating_splits
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hfin : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K L)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hgen : Subgroup.closure {d : ClassGroup (𝓞 K) |
      ∃ 𝔮 ∈ S, d = ClassGroup.mk0 ⟨𝔮.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔮.ne_bot⟩} = ⊤)
    (hsplit : ∀ 𝔮 ∈ S, (𝔮.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    Idele.normClassSubgroup K L = ⊤ := by
  classical
  have hker : (IdeleClassGroup.idealClassHom K).ker ≤ Idele.normClassSubgroup K L := by
    rw [IdeleClassGroup.ker_idealClassHom K]
    exact Subgroup.map_mono (integralIdelesLeNormImage (K := K) (L := L) hfin hinf)
  have hS : ∀ d ∈ ({d : ClassGroup (𝓞 K) |
      ∃ 𝔮 ∈ S, d = ClassGroup.mk0 ⟨𝔮.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔮.ne_bot⟩} : Set _),
      d ∈ (Idele.normClassSubgroup K L).map (IdeleClassGroup.idealClassHom K) := by
    rintro d ⟨𝔮, h𝔮, rfl⟩
    have hmem : IdeleClassGroup.mk K (HeckeL.ideleOfPrime K 𝔮) ∈
        Idele.normClassSubgroup K L :=
      Subgroup.mem_map_of_mem (IdeleClassGroup.mk K)
        (NK.GlobalCFTdeep.SecondInequality.ideleOfPrime_mem_normImage_of_splitsCompletely
          (K := K) (L := L) 𝔮 (hsplit 𝔮 h𝔮))
    have h2 := Subgroup.mem_map_of_mem (IdeleClassGroup.idealClassHom K) hmem
    rwa [idealClassHom_mk_ideleOfPrime K 𝔮] at h2
  have himg : (IdeleClassGroup.idealClassHom K).range ≤
      (Idele.normClassSubgroup K L).map (IdeleClassGroup.idealClassHom K) := by
    rw [MonoidHom.range_eq_top.mpr (IdeleClassGroup.idealClassHom_surjective K), ← hgen]
    exact (Subgroup.closure_le _).mpr hS
  rw [eq_top_iff]
  intro x _
  have hx : IdeleClassGroup.idealClassHom K x ∈ (IdeleClassGroup.idealClassHom K).range := ⟨x, rfl⟩
  obtain ⟨n, hn, hnx⟩ := himg hx
  have hmem : x * n⁻¹ ∈ (IdeleClassGroup.idealClassHom K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnx.symm, mul_inv_cancel]
  have hx' : x = (x * n⁻¹) * n := by group
  rw [hx']
  exact Subgroup.mul_mem _ (hker hmem) hn

/-- **Consequence of the norm-kernel principle**: such an extension has degree one. -/
theorem finrank_eq_one_of_unramified_of_generating_splits
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (hfin : differentIdeal (𝓞 K) (𝓞 L) = ⊤)
    (hinf : IsUnramifiedAtInfinitePlaces K L)
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hgen : Subgroup.closure {d : ClassGroup (𝓞 K) |
      ∃ 𝔮 ∈ S, d = ClassGroup.mk0 ⟨𝔮.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔮.ne_bot⟩} = ⊤)
    (hsplit : ∀ 𝔮 ∈ S, (𝔮.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L) :
    Module.finrank K L = 1 := by
  have h := normClassSubgroup_eq_top_of_unramified_of_generating_splits (K := K) (L := L)
    hfin hinf hgen hsplit
  have hidx := NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L)
  rw [h, Subgroup.index_top] at hidx
  exact hidx.symm

/-! ## The reduction -/

/-- **The `p`-class field with prescribed splitting, from the existence theorem and the
splitting law.** -/
theorem exists_pClassField_of_inputs
    (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (χ : ClassGroup (𝓞 K) →* Multiplicative (ZMod p)) (hχ : χ ≠ 1)
    (hT : ∀ v ∈ T, χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1)
    (hEx : ∀ (V : Subgroup (IdeleClassGroup K)), V.FiniteIndex →
        IsOpen (V : Set (IdeleClassGroup K)) → V.index = p →
        (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ V →
        ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
          IsGalois K L ∧ Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p ∧
          differentIdeal (𝓞 K) (𝓞 L) = ⊤ ∧ IsUnramifiedAtInfinitePlaces K L)
    (hSplit : ∀ {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
        [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
        (𝔭 : HeightOneSpectrum (𝓞 K)),
        (∀ Q : HeightOneSpectrum (𝓞 L),
          Q.asIdeal.LiesOver 𝔭.asIdeal → Q.asIdeal.ramificationIdx (𝓞 K) = 1) →
        IdeleClassGroup.mk K (HeckeL.ideleOfPrime K 𝔭) ∈ Idele.normClassSubgroup K L →
        ∀ Q : HeightOneSpectrum (𝓞 L),
          Q.asIdeal.LiesOver 𝔭.asIdeal → Q.asIdeal.inertiaDeg (𝓞 K) = 1) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ Module.finrank K L = p ∧
      differentIdeal (𝓞 K) (𝓞 L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L ∧
      ∀ v ∈ T, Ideal.inertiaDegIn v.asIdeal (𝓞 L) = 1 := by
  classical
  have hidx : (classChar K p χ).ker.index = p := index_ker_classChar K p χ hχ
  have hfin : (classChar K p χ).ker.FiniteIndex := by
    refine Subgroup.finiteIndex_iff.mpr ?_
    rw [hidx]
    exact (Fact.out (p := p.Prime)).ne_zero
  have hint : (Idele.integralIdeles K).map (IdeleClassGroup.mk K) ≤ (classChar K p χ).ker :=
    integralIdeles_map_le_ker_classChar K p χ
  have hopen : IsOpen ((classChar K p χ).ker : Set (IdeleClassGroup K)) :=
    isOpen_of_le_isOpen (isOpen_map_integralIdeles K) hint
  obtain ⟨L, hF, hN, hA, hfd, hGal, hnorm, hdeg, hdiff, hinf⟩ :=
    hEx (classChar K p χ).ker hfin hopen hidx hint
  refine ⟨L, hF, hN, hA, hfd, hGal, hdeg, hdiff, hinf, ?_⟩
  -- the degree-`p` Galois group is cyclic, hence abelian
  haveI : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank K L, hdeg])
  haveI : IsMulCommutative (L ≃ₐ[K] L) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
    obtain ⟨k, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hg a)
    obtain ⟨l, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hg b)
    exact Commute.zpow_zpow_self g k l
  -- every prime of `T` splits completely
  intro v hv
  have hmem : IdeleClassGroup.mk K (HeckeL.ideleOfPrime K v)
      ∈ Idele.normClassSubgroup K L := by
    rw [hnorm, MonoidHom.mem_ker, classChar_apply, idealClassHom_mk_ideleOfPrime K v]
    exact hT v hv
  letI hMSA : MulSemiringAction (L ≃ₐ[K] L) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hunr : ∀ Q : HeightOneSpectrum (𝓞 L),
      Q.asIdeal.LiesOver v.asIdeal → Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro Q hQ
    rw [← Commons.NumberTheory.NumberField.ramificationIdx_one_iff_not_dvd_differentIdeal
      (E := K) (K := L) Q.asIdeal Q.isPrime]
    rw [hdiff]
    intro hdiv
    have hle : (⊤ : Ideal (𝓞 L)) ≤ Q.asIdeal := Ideal.dvd_iff_le.mp hdiv
    exact Q.isPrime.ne_top (le_antisymm le_top hle)
  obtain ⟨Q₀, hQ₀⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := K) (L := L) v
  haveI : Q₀.asIdeal.LiesOver v.asIdeal := hQ₀
  rw [Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal Q₀.asIdeal (L ≃ₐ[K] L)]
  exact hSplit v hunr hmem Q₀ hQ₀

/-! ## The target theorem

The target is assembled here from the two inputs, which are owned elsewhere in the fleet:

* `NK.CFTLib.Existence.classField_exists_primeIndex` (the existence theorem at prime index: an
  open index-`p` subgroup `V` of `C_K` containing the image of the integral idèles is the norm
  class subgroup of an everywhere unramified degree-`p` extension), given the ideal-theoretic
  Artin reciprocity law `NK.CFTLib.artinReciprocityIdeal_proved` and the global fundamental class
  `NK.CFTLib.fundamentalClassElement`;
* `NK.CFTLib.Existence.splitting_of_normClass` (the splitting law: for an unramified abelian
  `L/K`, membership of the class of the idèle of `𝔭` in `N_{L/K}C_L` forces `𝔭` to split
  completely), given `NK.CFTLib.artinReciprocityIdeal_proved`.

The proof below is the bookkeeping between these two inputs and the character `χ`: the kernel
`V = ker(classChar K p χ)` of the lifted character is an open index-`p` subgroup containing the
integral idèles (by `index_ker_classChar` and `integralIdeles_map_le_ker_classChar`), so
`classField_exists_primeIndex` supplies the field `L`; the degree-`p` Galois group is cyclic, hence
commutative, and the primes of `T` have their class of the idèle of the prime in `V = N_{L/K}C_L`
by the hypothesis `hT` on `χ`, so `splitting_of_normClass` gives inertia degree `1`. -/

/-- **Existence of the `p`-class field with prescribed splitting** (the existence half of the
Hilbert class field, `p`-part, Hilbert/Furtwängler). -/
theorem pClassField_exists (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (χ : ClassGroup (NumberField.RingOfIntegers K) →* Multiplicative (ZMod p)) (hχ : χ ≠ 1)
    (hT : ∀ v ∈ T, χ (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩) = 1) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      IsGalois K L ∧ Module.finrank K L = p ∧
      differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) = ⊤ ∧
      IsUnramifiedAtInfinitePlaces K L ∧
      ∀ v ∈ T, Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers L) = 1 := by
  classical
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
    NK.CFTLib.Existence.classField_exists_primeIndex (K := K)
      NK.CFTLib.artinReciprocityIdeal_proved NK.CFTLib.fundamentalClassElement p V hfin hopen
      hidx hint
  haveI : IsGalois K L := hGal
  haveI : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card (p := p) (by rw [IsGalois.card_aut_eq_finrank K L, hdeg])
  haveI : IsMulCommutative (L ≃ₐ[K] L) := by
    refine IsMulCommutative.of_comm fun a b => ?_
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
    obtain ⟨k, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hg a)
    obtain ⟨l, rfl⟩ := (Subgroup.mem_zpowers_iff).mp (hg b)
    exact Commute.zpow_zpow_self g k l
  refine ⟨L, hF, hN, hA, hfd, hGal, hdeg, hdiff, hinf, ?_⟩
  intro v hv
  refine NK.CFTLib.Existence.splitting_of_normClass NK.CFTLib.artinReciprocityIdeal_proved
    hdiff v ?_
  rw [hnorm, MonoidHom.mem_ker, classChar_apply, idealClassHom_mk_ideleOfPrime K v]
  exact hT v hv

/-! ## The drive interface

`CFTLib.PClassFieldExists` (`Submission/CFTLib/Interfaces.lean`) is the interface through which the
consumers (the Shafarevich/Erdős/Martinet workspaces) use the theorem; it differs from
`NK.CFTLib.pClassField_exists` only in packaging `differentIdeal = ⊤` and
`IsUnramifiedAtInfinitePlaces` as `CFTLib.IsUnramified`. -/

/-- **The drive interface `CFTLib.PClassFieldExists`** (existence of the `p`-class field with
prescribed splitting), from `NK.CFTLib.pClassField_exists`. -/
theorem pClassFieldExists : CFTLib.PClassFieldExists :=
  fun K _ _ p _ T χ hχ hT => by
    obtain ⟨L, hF, hN, hA, hfd, hGal, hdeg, hdiff, hinf, hsplit⟩ :=
      pClassField_exists K p T χ hχ hT
    exact ⟨L, hF, hN, hA, hfd, hGal, hdeg, ⟨hdiff, hinf⟩, hsplit⟩

end NK.CFTLib
