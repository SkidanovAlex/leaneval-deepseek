import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Route B: the global fundamental class for ALL finite Galois `L/K` from cyclic reciprocity

This module contains **no declarations**; it is the written-out plan (and the record of what is
*not* true) for the three lemmas into which

```lean
theorem fcElement_of_primePowerReciprocity (hpp : NK.CFTLib.PrimePowerReciprocity) :
    NK.GlobalCFTdeep.FundamentalClassElement
```

is split.  The target says: for every finite Galois extension `L/K` of number fields,
`H²(Gal(L/K), C_L)` contains an element of order `[L:K]` (`C_L = 𝕀_L ⧸ Lˣ`).

## The reduction (Milne, *CFT*, VIII.4; NSW XII, proof of (12.2.1))

Write `n = [L:K]`.  Let `M/K` be a **cyclic** extension of degree `n` with `L ∩ M = K`, and put
`Ω = LM`, so `G := Gal(Ω/K) ≅ Gal(L/K) × Gal(M/K)`, `Nsub := Gal(Ω/L) ≅ Gal(M/K)`,
`Msub := Gal(Ω/M) ≅ Gal(L/K)`.  Then:

* `inf : H²(G/Msub, C_Ω^{Msub}) → H²(G, C_Ω)` is injective (`H¹ = 0`, `H1All` + the five-term
  sequence, `Commons.…H2_inflation_injective_of_subsingleton_H1`);
* `ker(res_Nsub) = range(inf)` (`Commons.…H2_inflation_restriction_exact_of_subsingleton_H1`);
* `x := C_Ω^{Msub} ≅ C_M`, and `hpp` produces an element of `H²(G/Msub, C_Ω^{Msub})` of order `n`
  (`NK.CFTLib.exists_fundamentalClass_of_isCyclic`);
* `H²(G/Nsub, C_Ω^{Nsub})` has exponent dividing `n`
  (`Commons.…natCard_nsmul_H2_eq_zero`, `Nat.card (G/Nsub) = n`).

So `Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res`
gives an element of order `n` in `H²(G/Nsub, C_Ω^{Nsub}) ≅ H²(Gal(L/K), C_L)`, provided

  (**)  `range(inf_Msub) ≤ ker(res_Nsub)`.

This is the *unique* remaining input, and it is the arithmetic input: by the Mackey formula for
restriction of inflation (`res_Nsub ∘ inf_Msub` is the map induced by the group isomorphism
`Nsub ≅ G/Msub` and the coefficient map `C_M = C_Ω^{Msub} ↪ C_Ω`), (**) is **equivalent** (via the
canonical `Ĥ⁰ ≅ Ĥ²` isomorphism on the two cyclic levels, i.e. the `H0`-computation) to

  (**')  `C_K ⊆ N_{Ω/L} C_Ω`   (as subgroups of `C_L`).

## The arithmetic: why (**') holds

For `x ∈ C_K ⊆ C_L` one wants `x ∈ N_{Ω/L}C_Ω = ker(θ_{Ω/L})`, where `θ_{Ω/L} : C_L → Gal(Ω/L)`
is the reciprocity isomorphism of the cyclic extension `Ω/L` (which `hpp` provides).  Writing
`θ = Artin`, and computing the global Artin symbol as the product of the local Artin symbols,
the classical functoriality of local class field theory gives, for a place `v` of `K`, the
Euler-place `z | v` of `L` and `x_v ∈ K_vˣ ⊆ L_zˣ`:

    θ_{Ω_𝒵/L_z}(i(x_v)) = θ_{M_w/K_v}(x_v)^{[L_z:K_v]} ,      [L_z:K_v] = e_z·f_z,

(equivalently: `x_v` is a norm from `Ω_𝒵` over `L_z` iff `x_v^{e f}` is a norm from `M_w` over
`K_v`; this uses the local norm-compatibility `θ_{E/F}∘N_{F'/F} = θ_{E/F'}` of local CFT and the
decomposition `Gal(Ω_𝒵/K_v) = Gal(L_z/K_v) × Gal(M_w/K_v)`, the latter being the local form of
`L ∩ M = K`).  Taking the product over all `z | v` and using `Σ_{z|v} e_z f_z = [L:K] = n`:

    θ_{Ω/L}(i(x)) = Π_v θ_{M/K}(x^{(v)})^n = θ_{M/K}(x)^n = 1 ,

the last step because `Gal(M/K) ≅ ℤ/n`.  Hence (**').

## Traps (recorded so that nobody re-derives them)

* The *local–global principle* for the norm group of the idèle class group is **FALSE**:
  `C_K ⊆ N_{Ω/L}C_Ω` holds here, yet an element of `C_K` need not be a local norm at *every*
  place.  Example: `K = ℚ`, `L = ℚ(√2)`, `M = ℚ(√5)`, `Ω = ℚ(√2,√5)`, `x =` the class of the
  idèle `7` (`7` splits in `L`, is inert in `M`): at the two places `z | 7` the component `7`
  is not a norm from `Ω_z` over `L_z` (odd valuation in an unramified quadratic), yet
  `θ_{Ω/L}(x) = Frob² = 1`.  So the "Hasse principle for `C_L/N C_Ω`" (as opposed to the Hasse
  norm theorem for *elements* of `Lˣ`, which is `NK.GlobalCFTdeep.hasseNormTheorem`) cannot be
  used; the Artin-symbol computation above is what is needed.
* The "obvious-looking" identity `θ_{Ω/L}(i(x)) = θ_{M/K}(x)` (no `n`-th power) is **FALSE**: take
  `K = ℚ`, `L = ℚ(√2)`, `M = ℚ(√3)`, `Ω = ℚ(√2,√3)`, a rational prime `𝔭` that splits in `L`
  (`f_L = 1`, e.g. `𝔭 = 7`) and is inert in `M` (`f_M = 2`); then `[L_z:K_v] = 1` and both
  identities agree, but for a prime *inert* in `L` (`f_L = 2`) and ramified in `M`, one gets
  `θ_{Ω_𝒵/L_z}(i(x_v)) = θ_{M_w/K_v}(x_v)^{f_L}`, so the exponent is the full `e_z f_z` and the
  `n`-th power only appears after summing over `z | v`.  A "counterexample" that ignores this
  (e.g. `K = ℚ, L = ℚ(√2), Ω = ℚ(√2,√3)`, the class of the prime `5`) is a miscalculation: `5` is
  inert in `L` *and* in `M`, so `f(5) = 2` in `Ω`, `[Ω:L] = 2` and `5` **splits completely** in
  `Ω/L`, whence the Artin symbol is `1` (the two local factors are `Frob^{f_L} = Frob² = 1`).
* The class-formation axioms, the cyclic case, `H¹ = 0`, the order bound `|H²| ≤ n` and the
  second inequality do **not** formally imply the general case: the trivial formation `A_L = ℤ`
  satisfies all of them for all levels (including cyclicity of `C_K/N C_L` for cyclic levels)
  and fails the conclusion for `G = ℤ/2 × ℤ/2`; the arithmetic of `C_L` (i.e. (**')) must enter.

## The three delegated lemmas

1. `NK.CFTLib.RouteB.exists_auxiliary_galois_tower` — the auxiliary tower
   `E = L₀·M` with `L₀ ≅_K L`, `M/K` cyclic of degree `n`, `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤`.
   (Construction: `q` a prime with `q ≡ 1 mod n·[K:ℚ]`, `q` unramified in `L`, `K ∩ ℚ(ζ_q) = ℚ`;
   `M` = the degree-`n` subfield of `K(ζ_q)`; `K(ζ_q)/K` is totally ramified at the primes over
   `q` while `L/K` is unramified there, so `L ∩ M = K`.  Note: the cyclotomic structure of `M`
   is *not* part of the statement — the comparison does not need it — and stating it as
   `M ≤ K(ζ_q)` *inside* `E` would be false, since it forces `K(ζ_q) ⊆ E = L₀M` and hence
   `q - 1 ∣ n²`.)
2. `NK.CFTLib.RouteB.res_inf_le_ker_res_of_auxiliary` — the comparison (**).
3. `NK.CFTLib.RouteB.exists_iso_rep_res_autCongr` — transport of the representation `C_•` along
   an isomorphism `L ≃ₐ[K] L'` (needed to compare `H²(Gal(L₀/K), C_{L₀})` with the target
   `H²(Gal(L/K), C_L)`).
-/

namespace NK.CFTLib.RouteB

end NK.CFTLib.RouteB
/-
## The assembly (concrete Lean plan, to be carried out in
## `Submission/Work/CFTLib/RouteB/fcElement_of_primePowerReciprocity.lean`)

Given `hA := exists_auxiliary_galois_tower K L`, `hB := res_inf_le_ker_res_of_auxiliary`,
`hT := exists_iso_rep_res_autCongr` and `hpp`, prove the target as follows (all Lean names verified
to exist unless marked):

* `obtain ⟨E, hfE, hnfE, halgE, hfdE, hgalE, L₀, Mid, he, hgalM, hcycM, hcardM, hdisj, hsup⟩ := hA K L`
  and `letI` all the instance hypotheses.  Set `Msub := Mid.fixingSubgroup`,
  `Nsub := L₀.fixingSubgroup` (so `fixedField Msub = Mid`, `fixedField Nsub = L₀` by
  `IsGalois.fixedField_fixingSubgroup`).
* `hcardN : Nat.card (Gal(E/K) ⧸ Nsub) = Nat.card Gal(L/K)`: `IsGalois.normalAutEquivQuotient Nsub`
  gives `Gal(E/K) ⧸ Nsub ≃* Gal(↥L₀/K)`, and `AlgEquiv.autCongr e` (with `e : ↥L₀ ≃ₐ[K] L`, the
  `he`) gives `Gal(↥L₀/K) ≃* Gal(L/K)`, so `Nat.card_congr` twice.
* `hcycM : IsCyclic (Gal(E/K) ⧸ Msub)`: `MulEquiv.isCyclic` along
  `(IsGalois.normalAutEquivQuotient Msub).symm` from `hcycM : IsCyclic (↥Mid ≃ₐ[K] ↥Mid)`.
* `hcardM : Nat.card (Gal(E/K) ⧸ Msub) = Nat.card Gal(L/K)`: as `hcardN`, from `hcardM`.
* `hdisj'`, `hsup'` (the `fixedField` forms): `← IsGalois.fixedField_fixingSubgroup` on `hdisj`,
  `hsup`.
* `hle := hB hpp Msub Nsub hcardN hcardM hcycM hdisj' hsup'`.
* `h1M := NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup Msub`,
  `h1N := … Nsub`.
* The M-level element: `NK.CFTLib.exists_fundamentalClass_of_isCyclic hpp` applied to the
  extension `E / ↥Mid` gives `xM : H²(Gal(E/↥Mid), C_E)` with `addOrderOf xM = Nat.card Gal(E/↥Mid)`.
  Transport it into `H²(Gal(E/K) ⧸ Msub, (rep K E).quotientToInvariants Msub)` with
  `groupCohomology.mapIso` along `(IntermediateField.subgroupEquivAlgEquiv Msub)` (the group iso
  `↥Msub ≃* Gal(E/↥(fixedField Msub))`) and `NK.HassePrinciple.repIso_quotientToInvariants_fixedField Msub`.
* `n := Nat.card Gal(L/K)`.  `hkill : ∀ y, addOrderOf y ∣ n` from
  `Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero` and
  `addOrderOf_dvd_iff_nsmul_eq_zero` plus `hcardN`.
* `obtain ⟨y, hy⟩ := Commons.RepresentationTheory.GroupCohomology.exists_addOrderOf_eq_of_inf_range_le_ker_res
    Msub Nsub (IdeleClassGroup.rep K E) h1M h1N hle n hkill xM hxM`.
* Transport `y : H²(Gal(E/K) ⧸ Nsub, (rep K E).quotientToInvariants Nsub)` to
  `H²(Gal(L/K), C_L)`: first
  `NK.HassePrinciple.repIso_quotientToInvariants_fixedField Nsub` together with
  `groupCohomology.mapIso` along `IsGalois.normalAutEquivQuotient Nsub` gives the element in
  `H²(Gal(↥L₀/K), C_{L₀})`, then `hT e` together with `groupCohomology.mapIso` along
  `AlgEquiv.autCongr e` gives the element in `H²(Gal(L/K), C_L)`.  The order is preserved by
  `addOrderOf_injective` on the injective additive maps underlying these isos.

### The one remaining *bookkeeping* obligation inside the assembly

`exists_fundamentalClass_of_isCyclic` at the M-level produces an element of order
`Nat.card Gal(E/↥Mid)`, whereas the twist lemma wants the order to be `n = Nat.card Gal(L/K)` (the
same number, via the diamond `Mid ⊓ L₀ = ⊥`, `Mid ⊔ L₀ = ⊤` together with `Nat.card Gal(L/K) =
Nat.card (↥Mid ≃ₐ[K] ↥Mid) = hcardM`).  Concretely one proves
`Nat.card Gal(E/↥Mid) = Nat.card Gal(↥Mid/K)` from
`IntermediateField.subgroupEquivAlgEquiv Mid.fixingSubgroup` (`↥Msub ≃* Gal(E/↥Mid)`),
`IsGalois.card_aut_eq_finrank` (`|Gal(E/↥Mid)| = [E:↥Mid]`), the tower law
`Module.finrank_mul_finrank` and the degree formula for a compositum of linearly disjoint
subextensions (`IntermediateField.LinearDisjoint.of_inf_eq_bot` / `…finrank_sup`, in
`Mathlib/FieldTheory/LinearDisjoint.lean`) applied to `Mid` and `L₀` with `Mid ⊓ L₀ = ⊥`.
-/
/-
## Record: the verdict on `res_inf_le_ker_res_of_auxiliary` (prover, 2026-09-23)

The prover of `res_inf_le_ker_res_of_auxiliary` returned **declared FALSE / mis-stated**, with a
*correct* analysis of the situation:

* the implication `res_Nsub ∘ inf_Msub = 0  ⟺  C_K ⊆ N_{Ω/L₀}C_Ω` is right, and the conclusion is
  mathematically **true**;
* but it is *not derivable from `hpp` plus the abstract class-formation consequences*: the trivial
  formation `C_• = ℤ`, `G = (ℤ/2)²`, satisfies all of those and has the composite an isomorphism;
* the proof needs the missing infrastructure: the **global Artin map with its local description**,
  i.e. the compatibility/normalisation that the canonical reciprocity isomorphism
  `C_L ⧸ N_{Ω/L} C_Ω ≅ Gal(Ω/L)` produced by `hpp` (H⁰-computation + cyclic periodicity) is the
  classical Artin map whose local components are the local Artin symbols (equivalently: the
  Verlagerung/transfer identity `Artin_{Ω/L}∘i = Artin_{M/K}∘N_{L/K}`, which is the statement
  proved on paper in the section "The arithmetic" above).

So the reduction `hpp + (auxiliary tower) ⟹ fundamental class` is correctly *split*, and the
remaining gap is not a statement about the auxiliary tower but a **missing chapter**: the
local–global compatibility of the global Artin map (equivalently, `Artin` on principal idèles, the
product formula over places, and the functoriality `θ_{E/F}∘N_{F'/F} = θ_{E/F'}` of local CFT).
Everything downstream of that identity is already assembled here (the abstract twist
`exists_addOrderOf_eq_of_inf_range_le_ker_res`, the five-term sequence, `H1All`, the order bound).
-/
/-
## STATUS (end of this stretch)

**Proved (sorry-free, ready to import):**

* `NK.CFTLib.RouteB.exists_iso_rep_res_autCongr`
  (`Submission/Work/CFTLib/RouteB/exists_iso_rep_res_autCongr.lean`): the idèle class group
  representation is invariant under a field isomorphism `L ≃ₐ[K] L'`.  Helper modules live in
  `Submission/Work/CFTLib/RouteB/IdeleCongr/` (`PlaceCongr`, `localFieldCongr`, `ideleCongr`,
  `Assembly`).
* `NK.CFTLib.RouteB.exists_addOrderOf_eq_card_of_auxiliary`
  (`Submission/Work/CFTLib/RouteB/exists_addOrderOf_eq_card_of_auxiliary.lean`): **the cohomological
  assembly** — given the M-level element `x` of order `n` in
  `H²(Gal(Ω/K) ⧸ Msub, C_Ω^{Msub})` and the arithmetic input
  `hle : range(inf_Msub) ≤ ker(res_Nsub)`, it produces an element of order `n` of
  `H²(Gal(L/K), C_L)`.  This is the exact statement my deliverable needs downstream
  (`Commons.…exists_addOrderOf_eq_of_inf_range_le_ker_res` + `H1All` +
  `natCard_nsmul_H2_eq_zero` + the transports through `repIso_quotientToInvariants_fixedField` and
  `exists_iso_rep_res_autCongr`).

**In flight (delegated):**

* `NK.CFTLib.RouteB.exists_element_of_order_card_of_auxiliary` — the M-level element `x` from
  `hpp` (cheap: `exists_fundamentalClass_of_isCyclic` at the level `Ω^{Msub}/K` + `repIso`); it
  supplies the `x`/`hx` of the assembly above.
* `NK.CFTLib.RouteB.exists_auxiliary_galois_tower` — the auxiliary tower `E = L₀·M`
  (`M/K` cyclic of degree `n`, `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤`); helpers so far:
  `exists_cyclic_subfield_of_isCyclotomic`, `intersect_cyclotomic_eq_bot`.

**Missing (the honest gap):** the arithmetic input `hle` (`res_Nsub ∘ inf_Msub = 0`, equivalently
`C_K ⊆ N_{Ω/L}C_Ω`).  The prover's verdict (see above) is right: it is *not* a formal consequence of
`hpp`, and its proof needs the **global Artin map with its local description**: the normalisation
saying that the canonical reciprocity isomorphism of a cyclic level coming from `hpp`
(H⁰-computation + cyclic periodicity) has the local Artin symbols as its local components, hence
satisfies the Verlagerung identity `θ_{Ω/L}∘i = θ_{M/K}∘N_{L/K}`.  With that chapter in place, the
arithmetic input is derived exactly as in the section "The arithmetic" above; without it the
reduction stops at `hle`.

**Assembly recipe (concrete Lean) for the deliverable**, once `hle` is available:

```lean
-- in Submission/Work/CFTLib/RouteB/fcElement_of_primePowerReciprocity.lean
obtain ⟨E, hfE, …, L₀, Mid, he, hgalM, hcycM, hcardM, hdisj, hsup⟩ :=
  exists_auxiliary_galois_tower K L           -- set Msub := Mid.fixingSubgroup,
                                             -- Nsub := L₀.fixingSubgroup
have hcardN : Nat.card (Gal(E/K) ⧸ Nsub) = Nat.card Gal(L/K) := …   -- normalAutEquivQuotient + autCongr e
have hcycM' : IsCyclic (Gal(E/K) ⧸ Msub) := …                       -- MulEquiv.isCyclic
obtain ⟨x, hx⟩ := exists_element_of_order_card_of_auxiliary hpp Msub Nsub hcycM' hcardM …
obtain ⟨α, hα⟩ := exists_addOrderOf_eq_card_of_auxiliary Msub Nsub (e) hcardN x hx
                    (res_inf_le_ker_res_of_auxiliary hpp Msub Nsub …)  -- ← the missing arithmetic
exact ⟨⟨fun {K L} … => ⟨α, hα⟩⟩⟩
```
-/
