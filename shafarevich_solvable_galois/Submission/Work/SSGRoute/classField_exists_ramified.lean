import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.exists_normClassSubgroup_eq_of_kummer

/-!
# Existence of the class field of an arbitrary open subgroup of prime index

The existence theorem of global class field theory at prime index, **with no ramification
condition on `V`**: for a number field `K`, a prime `p`, and *any* open subgroup `V ≤ C_K` of index
`p`, there is a finite Galois extension `L / K` with `N_{L/K} C_L = V` and `[L : K] = p`.

This is `NK.CFTLib.Existence.classField_exists_primeIndex` with the hypothesis
`𝕀_K ≤ V` (i.e. `V` contains the integral idèles, i.e. `V` is unramified) dropped; the field is then
in general ramified.  The concrete consumers are the Grunwald/Shafarevich step lemmas of the
`SSGRoute` project, where the subgroup `V` coming from an arbitrary Galois extension of degree `p`
is not assumed to contain the integral idèles.

## Proof

Two cases.

* **`K` contains a primitive `p`-th root of unity.** Milne, *CFT*, 9.3
  (`exists_galois_normClassSubgroup_le_of_kummer`, the Kummer/`S`-units construction) produces a
  finite abelian extension `L₀ / K` with `N_{L₀/K}C_{L₀} ≤ V`; the norm-group correspondence at
  index `p` (`exists_intermediateField_normClassSubgroup_eq_of_index_prime`, Milne 9.1) produces a
  subfield `E ⊆ L₀` with `N_{E/K}C_E = V` and `[E : K] = p`.  `E/K` is Galois because `L₀/K` is
  abelian.  This is the lemma `exists_normClassSubgroup_eq_of_kummer`.

* **`ζ_p ∉ K`.** Pass to `K' = K(ζ_p)` (`exists_cyclotomicExtension_galois_isCyclic`), of degree
  prime to `p`, and apply the previous case to the pullback `V.comap (N_{K'/K})`, which again has
  index `p` (`index_comap_normClassHom_eq_prime`).  The resulting degree-`p` Galois `M / K'` is then
  descended along the cyclic extension `K'/K` by
  `exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg` (Milne 9.4, degree form), which
  explicitly assumes no unramifiedness.  The case `p = 2` cannot occur here, since `-1` is a
  primitive square root of unity in any number field.

The arithmetic inputs are the two hypotheses `hARL` (Lang reciprocity) and `hFC` (the fundamental
class), used only through the reciprocity isomorphism `index_normClassSubgroup_eq_finrank` and the
ideal-theoretic Artin map.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

theorem classField_exists_ramified (hARL : NK.CFTLib.ArtinReciprocityIdeal)
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    ∀ {K : Type} [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
      (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)), V.FiniteIndex →
      IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)) → V.index = p →
      ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (_ : FiniteDimensional K L),
        IsGalois K L ∧ NK.GlobalCFT.Idele.normClassSubgroup K L = V ∧ Module.finrank K L = p := by
  intro K _ _ p _ V hV hopen hidx
  classical
  by_cases h : ∃ ζ : K, IsPrimitiveRoot ζ p
  · -- `K` contains `ζ_p`: the Kummer case
    obtain ⟨ζ, hζ⟩ := h
    exact exists_normClassSubgroup_eq_of_kummer (K := K) hARL hFC p hζ V hV hopen hidx
  · -- `p ≠ 2`, since `-1` is a primitive second root of unity in any number field
    have hp2 : p ≠ 2 := by
      intro hp
      exact h ⟨-1, hp ▸ IsPrimitiveRoot.neg_one (R := K) 0 (by norm_num)⟩
    obtain ⟨K', hFK', hNK', hAK', hfdK', ζ, hζ, hgalK', hcommK', hcycK', hcop⟩ :=
      NK.CFTLib.Existence.exists_cyclotomicExtension_galois_isCyclic K p h
    letI : Algebra K K' := hAK'
    letI : FiniteDimensional K K' := hfdK'
    haveI : IsGalois K K' := hgalK'
    haveI : IsMulCommutative (K' ≃ₐ[K] K') := hcommK'
    haveI : IsCyclic (K' ≃ₐ[K] K') := hcycK'
    -- the index of `N_{K'/K}C_{K'}` is `[K' : K]`, prime to `p`, by reciprocity from `hFC`
    have hidxK' : (NK.GlobalCFT.Idele.normClassSubgroup K K').index = Module.finrank K K' :=
      NK.GlobalCFT.index_normClassSubgroup_eq_finrank
        (NK.GlobalCFTdeep.artinReciprocity_of_fundamentalClassElement hFC)
    have hcop' : ¬ p ∣ (NK.GlobalCFT.Idele.normClassSubgroup K K').index := by
      rw [hidxK']
      exact hcop
    -- the pullback `V.comap (N_{K'/K})` is again open of index `p`
    have hV'index : (V.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K')).index = p :=
      NK.CFTLib.Existence.index_comap_normClassHom_eq_prime (K := K) (K' := K') p V hidx hcop'
    have hV'fin : (V.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K')).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (by rw [hV'index]; exact (Fact.out : p.Prime).ne_zero)
    have hV'open : IsOpen ((V.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K') :
        Subgroup (NK.GlobalCFT.IdeleClassGroup K')) : Set (NK.GlobalCFT.IdeleClassGroup K')) :=
      NK.NUV2.ArtinBridge.isOpen_comap_normClassHom K K' V hopen
    -- the Kummer case over `K'`
    obtain ⟨M, hFM, hNM, hAM, hfdM, hgalM, hnormM, hdegM⟩ :=
      exists_normClassSubgroup_eq_of_kummer (K := K') hARL hFC p hζ
        (V.comap (NK.GlobalCFT.IdeleClassGroup.normClassHom K K')) hV'fin hV'open hV'index
    letI : Algebra K' M := hAM
    letI : FiniteDimensional K' M := hfdM
    haveI : IsGalois K' M := hgalM
    -- descend along the cyclic extension `K'/K`
    exact NK.CFTLib.Existence.exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg
      (K := K) (K' := K') hARL hFC hcop hp2 hζ V hidx hnormM hdegM

end Work.SSGRoute
