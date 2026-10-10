import Mathlib.Order.CompletePartialOrder
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.CFTLib.GFC.exists_auxiliary_galois_tower
import Submission.NK.GFC.fundamentalClassElement_of_cyclotomicTower
import Submission.NK.GFC.normImage_of_auxiliary_cyclotomic

/-! # The global fundamental class (Milne, *Class Field Theory*, VIII.4 Theorem 4.7)

The target `NK.GlobalCFTdeep.FundamentalClassElement` asks: for every finite Galois extension
`L / K` of number fields, `H²(Gal(L/K), C_L)` contains an element of order `[L:K]`, where
`C_L = 𝕀_L ⧸ Lˣ` is the idèle class group.

## What is available unconditionally in this workspace

* `NK.GlobalCFTdeep.natCard_groupCohomology_two_le_card` — `H²(Gal(L/K), C_L)` is finite of order
  `≤ [L:K]` (Milne 5.1(c));
* `NK.GlobalCFTdeep.H1All.subsingleton_groupCohomology_one_ideleClassGroup` — `H¹ = 0` at every
  level;
* `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic` — the norm index `[C_K : N_{L/K}C_L] = [L:K]`
  for cyclic `L/K`;
* `Submission/Work/CFTLib/fundamentalClassInputs.lean` — the unconditional reduction of the
  **cyclic** case to `NK.CFTLib.PrimePowerReciprocity` (Artin reciprocity for cyclic extensions
  of prime-power degree), which is **proved** in this workspace
  (`CFTLib/isCyclic_normClassQuotient_of_primePower.lean`): hence
  `NK.CFTLib.exists_fundamentalClass_of_isCyclic` gives, for every *cyclic* `L/K`, an element of
  order `[L:K]` in `H²(Gal(L/K), C_L)`.

## The general (non-cyclic) case: Route B

For general `L/K` the two groups `C_K ⧸ N_{L/K}C_L ≅ Gal(L/K)ᵃᵇ` and `H²(Gal(L/K), C_L)` differ
(Milne's Remark 5.5), and the class-formation axioms alone cannot give the fundamental class (the
trivial module `ℤ` satisfies `H¹(H,ℤ) = 0` and `|H²(H,ℤ)| ≤ |H|` for all `H`, with equality for
cyclic `H`, yet `H²(G,ℤ) = Gᵃᵇ` is not cyclic of order `|G|` for `G = ℤ/2 × ℤ/2`).

The argument implemented here is Milne VIII.4 Theorem 4.7 (the classical "compare `L` with a cyclic
extension of the same degree" argument):

* `NK.CFTLib.GFC.exists_auxiliary_galois_tower` — the auxiliary tower: an overfield `E ⊇ L₀ · M`
  with `L₀ ≅_K L` and `M/K` **cyclic** of degree `n = [L:K]`, `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤`;
* the cyclic fundamental class at the level `M/K`
  (`NK.CFTLib.GFC.exists_element_of_order_card_of_auxiliary`);
* the abstract twist
  (`Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res`),
  packaged as `NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary`, which needs the single
  arithmetic input

  `NK.CFTLib.fundamentalClassArithmeticInput`:
  `range(inf_{Msub}) ≤ ker(res_{Nsub})`, equivalently (in Milne's language) `C_K ⊆ N_{Ω/L}C_Ω`.

The remaining statement is exactly the reciprocity law for the cyclic extension `Ω/L` (Milne V.5.3,
Lang X.2); it is stated here in the form in which the cohomological assembly consumes it.
-/

/-! ## State of this file, and the two routes to the remaining gap

**Assembled here, unconditionally and sorry-free**:  the whole reduction of the general
(non-cyclic) case to a single arithmetic input.  Concretely, given

* `NK.CFTLib.PrimePowerReciprocity` (proved: `CFTLib/isCyclic_normClassQuotient_of_primePower.lean`),
* the auxiliary tower `NK.CFTLib.GFC.exists_auxiliary_galois_tower` (proved),
* the cyclic fundamental class at the auxiliary level
  (`NK.CFTLib.GFC.exists_element_of_order_card_of_auxiliary`, proved) and
* the abstract twist `NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary` (proved),

`fundamentalClassElement_of_arithmeticInput` below produces the fundamental class, and its only
hypothesis is `fundamentalClassArithmeticInput` — the arithmetic input (**) of
`CFTLib/RouteB/plan.lean`.

**The remaining gap** `fundamentalClassArithmeticInput` is *equivalent*
`NK.CFTLib.Translation.inf_range_le_ker_res_of_norm` (delegated) to the statement

  (**')  `C_K ⊆ N_{Ω/L}C_Ω`,

i.e. to the reciprocity law for the *cyclic* auxiliary extension `Ω/L`.  Two routes to it:

**Route 1 (in flight, by the team).**  The ideal-theoretic reciprocity law
`NK.CFTLib.ArtinReciprocityIdeal` (`CFTLib/ArtinIdeal.lean`, in flight as
`CFTLib/ArtinReciprocityIdeal/*`, the remaining obligation being the cyclic case
`artinSymbolKillsPrincipal_cyclic`, Childress Ch. 5 / Lang X.2) together with the idèlic Artin map
built from it (`CFTLib/Arl/`, in flight).  There, `(**)` is the statement called `hle` in
`CFTLib/Arl/STATUS.md`.

**Route 2 (unconditional, no general reciprocity law needed — recommended).**  The auxiliary
tower of Route B is *cyclotomic*: the proof of `exists_auxiliary_galois_tower` builds
`M ⊆ K(ζ_q)` for a prime `q` with `K ∩ ℚ(ζ_q) = ℚ`, and the ambient field is `E = L₀ ⊔ M`.  Hence
`E/L₀` is a *subextension of the cyclotomic extension* `L₀(ζ_q)/L₀`, and the **cyclotomic case of
the reciprocity law is available unconditionally** in this workspace
(`NK.CFTLib.artinKillsPrincipal_of_le_isCyclotomicExtension`, with base case
`NK.CFTLib.ARL.artinReciprocity_cyclotomic`) — this is precisely what
`NK.GFC.exists_auxiliary_galois_tower_cyclotomic` (delegated) records.  With it:

1. `ψ_{E/L₀}(𝔞𝒪_{L₀}) = ψ_{E/K}(𝔞^{[L₀:K]}) = 1` for every ideal `𝔞` of `K`, *elementarily*
   (Frobenius functoriality and `Σ_𝔮 e·f = [L₀:K] = |Gal(M/K)|`; this is the computation recorded
   in the guidance of `CFTLib/fcElement_of_arl.lean`);
2. `ker ψ_{E/L₀} = P_c(L₀)·N_{E/L₀}(I_E)` for the cyclotomic modulus `c`, from the cyclotomic
   case, the elementary `frobAtPrime_prod_relNorm_eq_one.lean` (`N ⊆ ker`) and the index equality
   `[I : P_c·N] ≤ [C_{L₀} : N C_E] = [E:L₀]` (`index_eq_finrank_of_isCyclic`, proved);
3. the idèlic Artin map of `E/L₀` built from the cyclotomic case by the construction of
   `CFTLib/Arl/exists_monoidHom_ideleArtin.lean` (whose only input, its `Crux`
   `artinSym_spanSingleton_eq_one`, is *exactly* the cyclotomic case here) has
   `ker = L₀ˣ · N_{E/L₀} 𝕀_E`: it kills `L₀ˣ` (the cyclotomic case through the congruence
   adjustment `exists_isCongruenceSubgroup_and_adjust`) and kills the norm idèles *elementarily*
   (`art(Ny) = ψ(N(ideal y)·(b)) = 1` by `frobAtPrime_prod_relNorm_eq_one` and the Case); it is
   surjective (Frobenius generation, `SecondFrobenius...frobeniusGenerateTop_of_notMem`), and both
   `ker` and `L₀ˣ·N𝕀_E` have index `[E:L₀]` in `𝕀_{L₀}` (`index_eq_finrank_of_isCyclic`);
4. hence for `x ∈ C_K` (embedded in `C_{L₀}`) one has `art(i x) = ψ(𝔞𝒪_{L₀}) = 1` by (1), so
   `i x ∈ ker art = L₀ˣ·N 𝕀_E`, i.e. `x ∈ N_{E/L₀}C_E` = (**').

The pieces 3–4 are the "idèlic Artin map" development in `CFTLib/Arl/`; the *only* difference from
the team's Route 1 is that the ideal-theoretic input is the **cyclotomic** case (proved) rather
than the general `ArtinReciprocityIdeal` (in flight).  A colleague can therefore discharge
`fundamentalClassArithmeticInput` by running the `CFTLib/Arl/` construction with the cyclotomic
case, or by proving (**') for the tower and applying
`NK.CFTLib.Translation.inf_range_le_ker_res_of_norm`.
-/

/-! ## Note (project lead, this session): the approximation trick for (**')

The project lead's route for (**') `C_K ⊆ N_{Ω/L}C_Ω` avoids ramified local–global compatibility:
the local norm groups `N(Ω_w^×)` are open of finite index in `L_w^×` (local norm index theorem), so
for `x ∈ C_K` one chooses `a ∈ K^×` by weak approximation with `a·x_w ∈ N(Ω_w^×)` at every place
`w` of `L` ramified in `Ω` (and at the places dividing the modulus), whence `a x` is a local norm
everywhere; the remaining ideal part `𝔟` of `a x` satisfies
`ψ_{Ω/L}(𝔟𝒪_L) = ψ_{M/K}(N_{L/K}(𝔟𝒪_L)) = ψ_{M/K}(𝔟)^n = 1` by *unramified* Frobenius
functoriality (`n = [M:K]` kills `Gal(M/K)`), and `ker ψ_{Ω/L} = P_{m,+}·N(I_Ω)` (reciprocity law
for the cyclic `Ω/L` + surjectivity + the index `= [Ω:L]`) puts `𝔟` in the norm group.

In Route 2 below, the reciprocity law needed for `Ω/L` is the **cyclotomic case**, which is proved
unconditionally in this workspace — the auxiliary `Ω/L` produced by the Route B construction is a
subextension of a cyclotomic extension.  The general `ArtinReciprocityIdeal` is therefore *not*
needed here (it would only be needed for an auxiliary tower that is not cyclotomic, i.e. for the
Route B statement in its general form).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

/-- **The arithmetic input of the general case of the fundamental class.**

For an auxiliary tower `Msub, Nsub ⊴ Gal(Ω/K)` with complementary fixed fields (as produced by
`NK.CFTLib.GFC.exists_auxiliary_galois_tower`), the image of the inflation along `Msub` is
contained in the kernel of the restriction along `Nsub`.

Equivalently (Milne, *CFT*, VIII.4; the Mackey formula plus the `H⁰`-computation of class field
theory): `C_K ⊆ N_{Ω/L}C_Ω` as subgroups of `C_L` — the reciprocity law for the cyclic extension
`Ω/L`. -/
def fundamentalClassArithmeticInput : Prop :=
  ∀ {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω] (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal]
    [Nsub.Normal],
    Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K) →
    Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K) →
    IsCyclic (Gal(Ω/K) ⧸ Msub) →
    IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥ →
    IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤ →
    LinearMap.range
        ((groupCohomology.infNatTrans ℤ Msub 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom ≤
      LinearMap.ker
        ((groupCohomology.resNatTrans ℤ (G := Nsub) (H := Gal(Ω/K)) Nsub.subtype 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom

/-- **The cohomological assembly of Route B**: the cyclic fundamental class at the auxiliary level
plus the arithmetic input gives the fundamental class at the level `L/K`. -/
theorem fundamentalClassElement_of_arithmeticInput (hpp : NK.CFTLib.PrimePowerReciprocity)
    (h : fundamentalClassArithmeticInput) : NK.GlobalCFTdeep.FundamentalClassElement := by
  refine ⟨fun {K L} _ _ _ _ _ _ _ => ?_⟩
  classical
  obtain ⟨E, hfE, hnfE, halgE, hfdE, hgalE, L₀, Mid, he, hgalM, hcycM, hcardM, hdisj, hsup⟩ :=
    NK.CFTLib.GFC.exists_auxiliary_galois_tower K L
  letI : Algebra K E := halgE
  letI : FiniteDimensional K E := hfdE
  letI : IsGalois K E := hgalE
  obtain ⟨e⟩ := he
  haveI : IsGalois K ↥L₀ := IsGalois.of_algEquiv e.symm
  let Msub : Subgroup Gal(E/K) := Mid.fixingSubgroup
  let Nsub : Subgroup Gal(E/K) := L₀.fixingSubgroup
  haveI : Msub.Normal := inferInstance
  haveI : Nsub.Normal := inferInstance
  have hfixM : IntermediateField.fixedField Msub = Mid :=
    IsGalois.fixedField_fixingSubgroup (F := K) (E := E) Mid
  have hfixN : IntermediateField.fixedField Nsub = L₀ :=
    IsGalois.fixedField_fixingSubgroup (F := K) (E := E) L₀
  have hcardN : Nat.card (Gal(E/K) ⧸ Nsub) = Nat.card Gal(L/K) := by
    have h1 : Nat.card (Gal(E/K) ⧸ Nsub) =
        Nat.card Gal(↥(IntermediateField.fixedField Nsub)/K) :=
      Nat.card_congr (IsGalois.normalAutEquivQuotient Nsub).toEquiv
    have h2 : Nat.card Gal(↥(IntermediateField.fixedField Nsub)/K) = Nat.card Gal(↥L₀/K) := by
      rw [hfixN]
    have h3 : Nat.card Gal(↥L₀/K) = Nat.card Gal(L/K) :=
      Nat.card_congr (AlgEquiv.autCongr e).toEquiv
    exact h1.trans (h2.trans h3)
  have hcycM' : IsCyclic (Gal(E/K) ⧸ Msub) := by
    have : IsCyclic Gal(↥(IntermediateField.fixedField Msub)/K) := by
      rw [hfixM]
      exact hcycM
    exact (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient Msub)).mpr this
  have hcardM' : Nat.card (Gal(E/K) ⧸ Msub) = Nat.card Gal(L/K) := by
    have h1 : Nat.card (Gal(E/K) ⧸ Msub) =
        Nat.card Gal(↥(IntermediateField.fixedField Msub)/K) :=
      Nat.card_congr (IsGalois.normalAutEquivQuotient Msub).toEquiv
    have h2 : Nat.card Gal(↥(IntermediateField.fixedField Msub)/K) = Nat.card Gal(↥Mid/K) := by
      rw [hfixM]
    exact h1.trans (h2.trans hcardM)
  have hdisj' : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥ := by
    rw [hfixM, hfixN, inf_comm]
    exact hdisj
  have hsup' : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤ := by
    rw [hfixM, hfixN, sup_comm]
    exact hsup
  obtain ⟨x, hx⟩ :=
    NK.CFTLib.GFC.exists_element_of_order_card_of_auxiliary hpp Msub Nsub hcycM' hcardM'
      hdisj' hsup'
  exact NK.CFTLib.GFC.exists_addOrderOf_eq_card_of_auxiliary Msub Nsub (hfixN ▸ e) hcardN x hx
    (h Msub Nsub hcardN hcardM' hcycM' hdisj' hsup')

/-- **The global fundamental class** (Milne, *CFT*, VIII.4 Theorem 4.7): for every finite Galois
extension of number fields `L/K`, `H²(Gal(L/K), C_L)` contains an element of order `[L:K]`.

The proof is Route 2 of the header: the auxiliary tower with its cyclotomic structure
(`NK.GFC.exists_auxiliary_galois_tower_cyclotomic`), the arithmetic input of Route B for that
tower (`NK.GFC.normImage_of_auxiliary_cyclotomic`, whose proof uses the *cyclotomic* case of the
reciprocity law, available unconditionally) and the `H⁰`/`H²` translation
(`NK.CFTLib.Translation.inf_range_le_ker_res_of_norm`), assembled by
`NK.GFC.fundamentalClassElement_of_cyclotomicTower`. -/
theorem fundamentalClassElement : NK.GlobalCFTdeep.FundamentalClassElement :=
  NK.GFC.fundamentalClassElement_of_cyclotomicTower NK.CFTLib.primePowerReciprocity
    (by
      -- the arithmetic input of Route B for the auxiliary tower produced by
      -- `NK.GFC.exists_auxiliary_galois_tower_cyclotomic`: the cyclotomic case of the
      -- reciprocity law, in the `H⁰` form `C_K ⊆ N_{E/L₀}C_E`.
      intro K E _ _ _ _ _ _ _ L₀ M _ _ hdisj hsup hcard hcyc _ Ω _ _ _ _ _ q hq hcycΩ φ hφ
      exact NK.GFC.normImage_of_auxiliary_cyclotomic L₀ M hdisj hsup hcard hcyc Ω q hq hcycΩ
        φ hφ)

end NK.CFTLib
