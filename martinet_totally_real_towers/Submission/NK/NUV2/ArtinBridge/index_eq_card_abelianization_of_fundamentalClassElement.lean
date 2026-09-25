import Mathlib
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.NUV2.ArtinBridge.nsmul_index_mem_norm_range
import Submission.NK.NUV2.ArtinBridge.eq_zero_of_forall_prime_exists_nsmul_eq_zero
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_universe_bridge
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.GlobalCFTdeep.SecondInequality.normClassSubgroup_index_eq_natCard_H0
import Submission.NK.GlobalCFTdeep.HasseNormTheoremUniverse
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization
import Submission.Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_of_subsingleton_H1_H2_of_solvable

/-!
# The norm index of a finite Galois extension is the order of the abelianisation

Given the fundamental class element `hFC` (the irreducible arithmetic input of the global class
formation), for every finite Galois extension `L/K` of number fields the index of the norm class
subgroup `N_{L/K} C_L` in the idèle class group `C_K` is the order of the abelianisation of
`Gal(L/K)`:

  `[C_K : N_{L/K} C_L] = |Gal(L/K)^{ab}|`.

This is the "norm index theorem"/Artin reciprocity in index form for an arbitrary finite Galois
extension.

## The mathematical content of this file

The class-formation axioms (`NK.GlobalCFT.CohomologicalFieldAxiom`) and the `H⁰`-computation
identify the index with `|Ĥ⁰(G, C_L)|` (`NK.GlobalCFT.H0Computation.index_eq_natCard`), and
`Ĥ⁻²(G, ℤ) ≅ G^{ab}` is unconditional
(`Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization`).  So
everything rests on

  **Tate's theorem** (Milne, *Class Field Theory*, II.3.11): if `H¹(H,C) = 0` and `|H²(H,C)| = |H|`
  for all subgroups `H ≤ G` and `α ∈ H²(G,C)` has order `|G|`, then
  `Ĥ⁻²(G, ℤ) ≅ Ĥ⁰(G, C)`.

The library proves this only for **solvable** `G`
(`Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class`),
whereas the general Galois group `Gal(L/K)` is not solvable.  The missing ingredient is the
non-solvable case of Milne's Theorem II.3.10 ("a module with `H¹(H,-) = H²(H,-) = 0` for all `H`
is cohomologically trivial"), which this file supplies:

* `subsingleton_tateCohomology_of_subsingleton_H1_H2_of_pos`: degrees `r ≥ 1` (Milne 1.31 kills the
  cohomology by `|G|`, and restriction to a Sylow `p`-subgroup is injective on `p`-primary parts by
  the corestriction identity `Cor ∘ Res = [G : P]`);
* `subsingleton_tateCohomology_of_subsingleton_H1_H2_of_zero`: degree `0`, reduced to the
  degree-`1` statement by the acyclic-complex dimension shift
  (`Commons.RepresentationTheory.TateCohomology.acyclicShortComplex_shift_up`) together with the
  `[G : P] • x ∈ N_G` "conorm" lemma `NK.NUV2.ArtinBridge.nsmul_index_mem_norm_range`;
* `subsingleton_tateCohomology_of_subsingleton_H1_H2`: all degrees, the negative ones from the
  library's dimension-shifting induction
  (`Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_neg_of_posTateVanishing`).

From there `natCard_tateCohomology_eq_of_fundamental_class` is Tate's theorem for arbitrary finite
`G` (the library's proof, with the solvability hypothesis discharged), and the norm index theorem
follows as in `NK.GlobalCFT.Cohomology`.

The final statement of the file is at an arbitrary universe: the `Type 0` theorem is transported
to a number field in `Type u` along its `Shrink` model, using the invariance of the norm index under
compatible ring equivalences of extensions
(`NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv`), exactly as in
`NK.GlobalCFTdeep.hasseNorm_index_eq_universe`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace NK.NUV2.ArtinBridge

open Commons.RepresentationTheory.TateCohomology
open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-! ## The non-solvable case of Milne's Theorem II.3.10 -/

section MilneThreeTen

variable {G : Type} [Group G] [Fintype G]

/-- **Vanishing in positive degrees** (Milne II.3.10, `r ≥ 1`).  If `H¹(H,A) = 0 = H²(H,A)` for
every subgroup `H ≤ G` then `Ĥʳ(G,A) = 0` for every `r ≥ 1`.

Indeed `A` restricted to a Sylow `p`-subgroup `P` still satisfies the hypothesis, so by the proved
solvable case all of its Tate cohomology vanishes; the corestriction identity
`Cor ∘ Res = [G : P]` (with `p ∤ [G : P]`) forces every `p`-primary element of `Ĥʳ(G,A)` to die,
and `|G|` kills `Ĥʳ(G,A)` (`r ≥ 1`), so every element is `p`-primary for some `p` — whence
`Ĥʳ(G,A) = 0`. -/
theorem subsingleton_tateCohomology_of_subsingleton_H1_H2_of_pos (A : Rep.{0,0,0} ℤ G)
    (hA : Hyp A) : ∀ r : ℤ, 1 ≤ r → Subsingleton (tateCohomology A r) := by
  intro r hr
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ r)
  have hn : 1 ≤ n := by omega
  haveI : NeZero n := ⟨by omega⟩
  refine subsingleton_tateCohomology_of_subsingleton_groupCohomology A n ?_
  classical
  have hzero : ∀ x : groupCohomology A n, x = 0 := by
    intro x
    refine eq_zero_of_forall_prime_exists_nsmul_eq_zero x fun q hq => ?_
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨S⟩ := Sylow.nonempty (p := q) (G := G)
    haveI : Group.IsSolvable ↥(S : Subgroup G) := by
      haveI : Group.IsNilpotent ↥(S : Subgroup G) := IsPGroup.isNilpotent S.isPGroup'
      infer_instance
    refine ⟨(S : Subgroup G).index, Subgroup.index_ne_zero_of_finite, Sylow.not_dvd_index S, ?_⟩
    have hs : Subsingleton (tateCohomology (Rep.res (S : Subgroup G).subtype A) (n : ℤ)) :=
      subsingleton_tateCohomology_of_subsingleton_H1_H2_of_solvable
        (Rep.res (S : Subgroup G).subtype A)
        (hyp_restrict (S : Subgroup G) A hA) (n : ℤ)
    have hs2 : Subsingleton (groupCohomology (Rep.res (S : Subgroup G).subtype A) n) :=
      subsingleton_groupCohomology_of_subsingleton_tateCohomology
        (Rep.res (S : Subgroup G).subtype A) n hs
    have h := NU.cor_resNatTrans_comp_apply (S : Subgroup G) A n x
    have h0 : (ConcreteCategory.hom
        ((groupCohomology.resNatTrans ℤ (S : Subgroup G).subtype n).app A)) x = 0 :=
      hs2.elim _ _
    rw [show (ConcreteCategory.hom
          ((groupCohomology.resNatTrans ℤ (S : Subgroup G).subtype n).app A ≫
            NU.cor (S : Subgroup G) A n)) x
        = (ConcreteCategory.hom (NU.cor (S : Subgroup G) A n))
            ((ConcreteCategory.hom
              ((groupCohomology.resNatTrans ℤ (S : Subgroup G).subtype n).app A)) x)
        from ConcreteCategory.comp_apply _ _ x,
      h0, map_zero] at h
    exact h.symm
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

/-- **Vanishing in degree zero** (Milne II.3.10, `r = 0`).  If `H¹(H,A) = 0 = H²(H,A)` for every
subgroup `H ≤ G` then `Ĥ⁰(G,A) = 0`.

It suffices to prove `A.ρ.invariants ≤ LinearMap.range A.ρ.norm`.  For `x` fixed by `G` and every
prime `q` with Sylow `q`-subgroup `P`: the solvable case applied to `P` gives `Ĥ⁰(P,A) = 0`, i.e.
`x` is a `P`-norm, and then `[G : P] • x` is a `G`-norm
(`NK.NUV2.ArtinBridge.nsmul_index_mem_norm_range`).  Since `q ∤ [G : P]` for every prime `q`,
the elementary lemma `NK.NUV2.ArtinBridge.eq_zero_of_forall_prime_exists_nsmul_eq_zero` applied
in `A ⧸ N_G A` yields `x ∈ N_G A`. -/
theorem subsingleton_tateCohomology_of_subsingleton_H1_H2_of_zero (A : Rep.{0,0,0} ℤ G)
    (hA : Hyp A) : Subsingleton (tateCohomology A 0) := by
  classical
  letI : Module ℤ A.V := A.hV2
  refine subsingleton_tateCohomology_zero_of_invariants_le_range_norm A.ρ ?_
  intro x hx
  have hx' : ∀ g : G, A.ρ g x = x := (Representation.mem_invariants A.ρ x).mp hx
  have hkey : ∀ q : ℕ, q.Prime → ∃ n : ℕ, n ≠ 0 ∧ ¬ q ∣ n ∧ n • x ∈ LinearMap.range A.ρ.norm := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨S⟩ := Sylow.nonempty (p := q) (G := G)
    haveI : Group.IsSolvable ↥(S : Subgroup G) := by
      haveI : Group.IsNilpotent ↥(S : Subgroup G) := IsPGroup.isNilpotent S.isPGroup'
      infer_instance
    have hvan : Subsingleton (tateCohomology (Rep.res (S : Subgroup G).subtype A) 0) :=
      subsingleton_tateCohomology_of_subsingleton_H1_H2_of_solvable _
        (hyp_restrict (S : Subgroup G) A hA) 0
    have hle := invariants_le_range_norm_of_subsingleton_tateCohomology_zero
      ((Rep.res (S : Subgroup G).subtype A).ρ) hvan
    have hxS : x ∈ ((Rep.res (S : Subgroup G).subtype A).ρ).invariants := by
      rw [Representation.mem_invariants]
      intro s
      exact hx' s.1
    have h2 : x ∈ LinearMap.range (((Rep.res (S : Subgroup G).subtype A).ρ).norm) := hle hxS
    have h3 : x ∈ LinearMap.range (∑ p : ↥(S : Subgroup G), A.ρ p.1) := h2
    have h4 := nsmul_index_mem_norm_range A.ρ (S : Subgroup G) hx' h3
    refine ⟨(S : Subgroup G).index, Subgroup.index_ne_zero_of_finite, Sylow.not_dvd_index S, ?_⟩
    simpa only [Representation.norm] using h4
  suffices h : (Submodule.Quotient.mk x : A.V ⧸ LinearMap.range A.ρ.norm) = 0 by
    simpa using (Submodule.Quotient.mk_eq_zero (LinearMap.range A.ρ.norm)).mp h
  refine eq_zero_of_forall_prime_exists_nsmul_eq_zero (Submodule.Quotient.mk x) fun q hq => ?_
  obtain ⟨n, hn0, hnq, hnmem⟩ := hkey q hq
  refine ⟨n, hn0, hnq, ?_⟩
  have key : (Submodule.mkQ (LinearMap.range A.ρ.norm)) (n • x)
      = n • (Submodule.Quotient.mk x : A.V ⧸ LinearMap.range A.ρ.norm) := by
    rw [map_nsmul, Submodule.mkQ_apply]
  rw [← key]
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range A.ρ.norm)).mpr hnmem

/-- **Milne's Theorem II.3.10 for an arbitrary finite group.**  If `H¹(H,A) = H²(H,A) = 0` for
every subgroup `H ≤ G`, then `Ĥʳ(G,A) = 0` for every `r ∈ ℤ`. -/
theorem subsingleton_tateCohomology_of_subsingleton_H1_H2 (A : Rep.{0,0,0} ℤ G) (hA : Hyp A) :
    ∀ r : ℤ, Subsingleton (tateCohomology A r) := by
  -- vanishing in all nonnegative degrees, for the group itself
  have hpos_all : ∀ r : ℤ, 0 ≤ r → Subsingleton (tateCohomology A r) := by
    intro r hr
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · subst hr0
      exact subsingleton_tateCohomology_of_subsingleton_H1_H2_of_zero A hA
    · exact subsingleton_tateCohomology_of_subsingleton_H1_H2_of_pos A hA r (by omega)
  -- the same vanishing after restriction to every subgroup, i.e. `PosTateVanishing A`
  have hvan : PosTateVanishing A := by
    classical
    intro H r hr
    rcases eq_or_lt_of_le hr with hr0 | hrpos
    · subst hr0
      exact subsingleton_tateCohomology_of_subsingleton_H1_H2_of_zero (Rep.res H.subtype A)
        (hyp_restrict H A hA)
    · exact subsingleton_tateCohomology_of_subsingleton_H1_H2_of_pos (Rep.res H.subtype A)
        (hyp_restrict H A hA) r (by omega)
  intro r
  by_cases hr : 0 ≤ r
  · exact hpos_all r hr
  · push_neg at hr
    exact subsingleton_tateCohomology_neg_of_posTateVanishing
      (fun K _ _ B hB => by
        intro r hr
        rcases eq_or_lt_of_le hr with hr0 | hrpos
        · subst hr0
          exact subsingleton_tateCohomology_of_subsingleton_H1_H2_of_zero B hB
        · exact subsingleton_tateCohomology_of_subsingleton_H1_H2_of_pos B hB r (by omega))
      A hvan r hr

end MilneThreeTen

/-! ## Tate's theorem (Milne II.3.11) for arbitrary finite groups -/

section TateTheorem

variable {G : Type} [Group G] [Fintype G]

/-- **Acyclicity of the splitting module**, without the solvability hypothesis: for a fundamental
class `α` of order `|G|`, the module `NU.Sprint C z` attached to a normalised cocycle `z`
representing `α` has vanishing Tate cohomology in every degree. -/
theorem subsingleton_tateCohomology_Sprint_of_H1_H2 (C : Rep.{0,0,0} ℤ G)
    (z : ↥(groupCohomology.cocycles₂ C)) (hz : ∀ g : G, z (g, 1) = 0)
    (α : groupCohomology C 2) (hzα : (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π C)) z = α)
    (hα : addOrderOf α = Nat.card G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card ↥H) :
    ∀ r : ℤ, Subsingleton (tateCohomology (NU.Sprint C z hz) r) :=
  subsingleton_tateCohomology_of_subsingleton_H1_H2 (NU.Sprint C z hz)
    (NU.subsingleton_H1_H2_res_ARep C z hz α hzα hα h1 h2)

/-- **Tate's theorem, cardinality form, for an arbitrary finite group** (Milne, *Class Field
Theory*, II.3.11): if `H¹(H,C) = 0` and `|H²(H,C)| = |H|` for every subgroup `H ≤ G` and
`α ∈ H²(G,C)` has order `|G|`, then `|Ĥ⁻²(G, ℤ)| = |Ĥ⁰(G, C)|`.

This is the library's `natCard_tateCohomology_eq_of_fundamental_class` with the hypothesis
`[Group.IsSolvable G]` discharged by `subsingleton_tateCohomology_of_subsingleton_H1_H2`. -/
theorem natCard_tateCohomology_eq_of_fundamental_class' (C : Rep.{0,0,0} ℤ G)
    (h1 : ∀ H : Subgroup G, Subsingleton (groupCohomology (Rep.res H.subtype C) 1))
    (h2 : ∀ H : Subgroup G, Nat.card (groupCohomology (Rep.res H.subtype C) 2) = Nat.card H)
    (α : groupCohomology C 2) (hα : addOrderOf α = Nat.card G) :
    Nat.card (tateCohomology (Rep.trivial ℤ G ℤ) (-2)) = Nat.card (tateCohomology C 0) := by
  obtain ⟨z, hzα, hz⟩ := NU.exists_normalized_cocycle C α
  have hacyc := subsingleton_tateCohomology_Sprint_of_H1_H2 C z hz α hzα hα h1 h2
  have hA1 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ (-1)) := hacyc (-1)
  have hA2 : Subsingleton ↥(tateCohomology (NU.AShortZ C z hz).X₂ ((-1 : ℤ) + 1)) :=
    hacyc ((-1 : ℤ) + 1)
  obtain ⟨e2⟩ :=
    tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.AShortZ C z hz) (NU.AShortZ_shortExact C z hz) (-1) hA1 hA2
  have hL1 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ (-2)) :=
    NU.subsingleton_tateCohomology_leftRegular G (-2)
  have hL2 : Subsingleton ↥(tateCohomology (NU.IShort (G := G)).X₂ ((-2 : ℤ) + 1)) :=
    NU.subsingleton_tateCohomology_leftRegular G ((-2 : ℤ) + 1)
  obtain ⟨e1⟩ :=
    tateCohomology_iso_of_acyclic_middle_of_subsingleton
      (NU.IShort (G := G)) (NU.IShort_shortExact (G := G)) (-2) hL1 hL2
  exact Nat.card_congr (e1.trans e2).toEquiv

end TateTheorem

/-! ## The norm index theorem at universe zero -/

open CategoryTheory in
/-- **The norm index theorem at universe `0`**: for a finite Galois extension of number fields,
`[C_K : N_{L/K} C_L] = |Gal(L/K)^{ab}|`, from the fundamental class element. -/
theorem index_eq_card_abelianization_of_fundamentalClassElement_typeZero
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      Nat.card (Abelianization (L ≃ₐ[K] L)) := by
  have h := NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement hFC (K := K) (L := L)
  obtain ⟨α, hα⟩ := h.fundamentalClass
  have hmain := natCard_tateCohomology_eq_of_fundamental_class' (NK.GlobalCFT.IdeleClassGroup.rep K L)
    h.h1_trivial h.h2_card α hα
  obtain ⟨e⟩ :=
    Commons.RepresentationTheory.TateCohomology.tateCohomology_neg_two_iso_abelianization (L ≃ₐ[K] L)
  rw [NK.GlobalCFT.H0Computation.index_eq_natCard
      (NK.GlobalCFT.globalCFT_H0Computation (K := K) (L := L)), ← hmain]
  exact Nat.card_congr e.toEquiv

/-! ## The norm index theorem at an arbitrary universe -/

/-- **The norm index theorem**: for a finite Galois extension of number fields in any universe,
the index of the norm class subgroup is the order of the abelianisation of the Galois group. -/
theorem index_eq_card_abelianization_of_fundamentalClassElement
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      Nat.card (Abelianization (L ≃ₐ[K] L)) :=
  index_eq_card_abelianization_universe_bridge
    (fun {K L} _ _ _ _ _ _ _ =>
      index_eq_card_abelianization_of_fundamentalClassElement_typeZero hFC (K := K) (L := L))

end NK.NUV2.ArtinBridge
