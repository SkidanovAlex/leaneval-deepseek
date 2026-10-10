import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.AuxExistsAssembly
import Submission.Work.SSGRoute.ZConstruction.ZDataGeneralGen
import Submission.Work.SSGRoute.zDataGeneralOfMupAndZeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The isolated arithmetic core of `Work.SSGRoute.shafarevich_z_construction`

`Work.SSGRoute.shafarevich_z_construction_of_zData` (module
`Submission.Work.SSGRoute.ZConstruction.ZDataBridge`) shows that the conclusion of
`Work.SSGRoute.shafarevich_z_construction` follows from the existence of a cochain `z` with
Schmidt--Wingberg's local data: additive and locally constant on `G_K`, agreeing with `y` on the
decomposition groups of the places of `cs(S)`, killing the involutions, unramified at every place
outside `cs(S)` that is not split in `Λ`, and satisfying the sharpened condition (b) triggered on
ramification at the places outside `cs(S)` that are split in `Λ`.

This file isolates exactly that existence statement as `Work.SSGRoute.z_data_general`.  It is the
*z*-half of Schmidt--Wingberg's Theorem 13 (arXiv:math/9809211, §4, pp. 13--20), in the form in
which the proof of `shafarevich_z_construction` consumes it; the same statement in the
one-dimensional case is `Work.SSGRoute.shafarevich_z_data_mup` /
`Work.SSGRoute.shafarevich_z_data_two` / `Work.SSGRoute.sw_z_exists_odd_sketch`, whose construction
is Schmidt--Wingberg's §4 argument:

* choose a sequence `z₁, z₂, … ∈ H¹(k_S|K, A)` with `z_i` ramified at exactly one new prime `P_i`
  (found by Chebotarev, `Work.SSGRoute.exists_split_place_avoiding` and its Frobenius variant),
  realising prescribed local data (the Tate--Poitou exactness `H¹(k_S|K, A) → ∏ H¹(K_P, A) →
  H¹(k_S|K, ℤ/p)^∨`, `tatePoitou_h1_realisation_sketch`);
* apply the pigeonhole principle to the Frobenius values and the Hilbert-symbol product formula to
  obtain the vanished conjugates (the odd-`p` case), with the three-term partition of the
  non-identity elements of `G(K|k)` in the case `p = 2`;
* for general `A`, induct on `dim_{𝔽_p} A`: with `A = A₀ ⊕ μ_p` and a class `z⁰` for `A₀` (the
  induction hypothesis), pass to the Galois closure `K̃` of the field cut out by `z⁰` and construct
  the auxiliary class `ỹ ∈ H¹(k_{S'}|K, μ_p)` by the Poitou--Tate diagram chase, then
  `z = z⁰ + inf z⁰⁰` satisfies (a) and (b) at every place.

Nothing in this file is proved; it records the single remaining obligation of the node
`Work.SSGRoute.shafarevich_z_construction`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!

## Obligation card (state of this node)

> **SESSION 34.**  This file no longer carries a `sorry`: the ramified obligation
> `Work.SSGRoute.z_data_general_of_ramified` (and with it the whole `z`-construction
> `Work.SSGRoute.z_data_general`) is *proved* --- but in `ZConstruction/ZDataFinal.lean`, which sits
> above this file, because the `p = 2` case of the ramified obligation needs the two-field narrow
> orthogonality `Work.SSGRoute.NoKimag.OrthHsplitTwoNarrow` (and hence the `NoKimag`/`ZDataTwo`/
> `H9Narrow` directories), which are above `ZDataGeneral` in the import DAG.  This file now keeps the
> *light* part of the construction:
> * `Work.SSGRoute.z_data_general_of_ramified_of_core_odd` --- the odd-`p` case of the ramified
>   obligation, from the Grünwald-with-escape realisation `Work.SSGRoute.zDataGeneralOfMupAndZeta`
>   with the odd `μ_p` core `Work.SSGRoute.z_data_mup_core` as the one-dimensional gate;
> * `Work.SSGRoute.z_data_general_of_unramified` and the gate-level wrappers
>   (`z_data_general_of_ramified_odd`, `z_data_general_of_realisationGate`, ...);
> * the two `μ_p` cores assembled into the one-dimensional gate `Work.SSGRoute.IsMupZData`
>   (`isMupZData_of_core_odd`, `isMupZData_of_core_two`, `isMupZData_of_cores`).
> The two statements `Work.SSGRoute.z_data_general` and
> `Work.SSGRoute.z_data_general_of_ramified` therefore now live in
> `Submission/Work/SSGRoute/ZConstruction/ZDataFinal.lean` (same statements as documented below, same
> names), and the node `Work.SSGRoute.shafarevich_z_construction` (which imports `ZDataFinal`)
> consumes them unchanged.

`Work.SSGRoute.z_data_general` is the *only* missing input of the node
`Work.SSGRoute.shafarevich_z_construction`: the latter is proved from it by the bridge
`Work.SSGRoute.shafarevich_z_construction_of_zData`
(`Submission/Work/SSGRoute/ZConstruction/ZDataBridge.lean`, sorry-free) plus
`Work.SSGRoute.cyclic_transfer_of_vanishing`
(`Submission/Work/SSGRoute/cyclic_transfer_of_vanishing.lean`, sorry-free).

**What has to be built.**  A cochain `z : Gal(Ω/k) → E` (viewed on `G_K = K.fixingSubgroup`, where
the action of `G_K` on `E` is trivial) with

1. `z` additive on `G_K` and locally constant there;
2. `z = y` on `D_A ⊓ G_K` for every place `A` conjugate into `S`;
3. `z c = 0` on the involutions `c ∈ G_K`;
4. `z` vanishes on the inertia of every place outside `cs(S)` that is not split in `Λ`;
5. at every place `B ∉ cs(S)`, split in `Λ`, at which `z` is ramified (non-zero on `I_B ⊓ G_K`):
   the image `z (D_B ⊓ G_K)` is cyclic, and `z` vanishes on the local group of every conjugate of
   `B` that is not a `G_K`-conjugate of `B` (Schmidt--Wingberg's `z_{σP} = 0`, `σ ≠ 1`).

**Where the content is.**  Conditions 1--3 are the "easy" part (the candidate `z := y` extended by
`0` off `G_K` satisfies 1--4 and, when `dim_{𝔽_p} E ≤ 1`, also 5 --- that is
`shafarevich_z_construction_of_finrank_le_one`).  For `dim_{𝔽_p} E ≥ 2` one must move the
ramification of `y` (which sits on the split-in-`Λ` places outside `cs(S)`) onto new primes at
split-in-`Λ` places outside `cs(S)`, each carrying a *cyclic* local component that vanishes on its
non-`G_K`-conjugate conjugates.  This is Schmidt--Wingberg §4:

* the sequence `z₁, z₂, … ∈ H¹(k_S|K, A)` whose members ramify at exactly one new prime `P_i`
  (Chebotarev: `Work.SSGRoute.exists_split_place_avoiding` and its Frobenius variant), each
  realising prescribed local data (the Tate--Poitou degree-1 realisation, still missing in the
  workspace);
* the pigeonhole principle on the Frobenius values and the Hilbert-symbol product formula, which
  give the vanished conjugates (`z^σ_P = 0`, `σ ≠ 1`) --- for odd `p` as `z = z_i + z_N`, for
  `p = 2` as a three-term sum with the partition of `G(K|k) ∖ {1}` into `G₁` (involutions), `G₂`,
  `G₃ = G₂⁻¹`;
* the induction on `dim_{𝔽_p} E` (the paper, pp. 18--19): with `E = E₀ ⊕ μ_p`, apply the induction
  hypothesis to `E₀`, let `K̃/k` be the Galois closure of the field cut out by the resulting class
  `z⁰`, replace `(Λ, T, S)` by `(K̃, T ∪ Ram(K̃|k), cs(K̃|k) ∪ T ∪ Ram(K̃|k))`, obtain the auxiliary
  class `ỹ ∈ H¹(k_{S'}|K, μ_p)` by the Poitou--Tate diagram chase, apply the *one-dimensional* case
  to `ỹ` to get `z⁰⁰`, and verify (a) and (b) for `z = z⁰ + inf z⁰⁰` (the new primes of `z⁰` lie in
  `cs(K̃|k)`, so `z⁰` is unramified outside `T'`, which is what makes the verification work).

**Fine points of the verification (paper, p. 18).**  Two facts make it work, and both are
consequences of the definitions rather than of the exactness statement:

* `z⁰` is unramified outside `T'(K)`, because the ramification of `z⁰` is *contained in the set of
  its new primes* (which lie over `S ∖ T(K) = cs(Λ|k)(K)`) together with `T(K)`, and all of these
  are ramified in the field `K'` cut out by `z⁰`; hence they lie over `Ram(K'|k) ⊆ Ram(K̃|k) ⊆ T'`;
* at a place `P ∉ T'(K)` where `z_P = z⁰_P + z⁰⁰_P` is ramified, `z⁰⁰_P` must be ramified (since
  `z⁰_P` is unramified), so by (b'') the underlying prime splits completely in `Λ' = K̃`, hence in
  `K'`; but `z⁰_P` becomes zero in `H¹(K'_Q, A₀) = H¹(K_{σP}, A₀)` for every `σ` (by definition of
  `K'` as the field cut out by `z⁰`), so `z^σ_P = z⁰⁰^σ_P = 0` and `z_P = z⁰⁰_P` is cyclic.

**Hypothesis-shape caveat for the induction (recorded after comparing with the paper).**  The
hypotheses of `z_data_general` are *not* those of Schmidt--Wingberg's Theorem 13: the paper assumes
`y` unramified at every `P ∉ T(K)` ((H1)) and `y_P = 0` for `P ∉ Ram(K|k) ∪ S_p ∪ S_1` ((H2)),
whereas the formalised statement assumes the *target's* conditions (`hyS`, `hyT`, `hy0`), under
which `y` may be ramified at places of `cs(S)` that are split in `K`, prime to `p` and unramified in
`Λ`.  Neither hypothesis set implies the other, and the formalised statement is the *stronger*
theorem.  Two consequences matter for the induction:

* the induction hypothesis *for the codimension-one component* can be applied to the component
  `y_L` of the given `y` (the hypotheses are componentwise), giving `z_L` with the target's
  conditions;
* but the verification of (b) for `z = z₀ + z_L` at the *new primes of `z₀`* requires the auxiliary
  class to **vanish** on the local groups of `T'∖T(K)` (not merely to be unramified there), and, in
  the paper, this auxiliary class is obtained by applying the one-dimensional case to the class
  `ỹ ∈ H¹(k_{S'}|K, μ_p)` which is *ramified at `T(K) ⊆ cs(S')(K)`* by construction.  Hence a
  one-dimensional input whose hypotheses include "vanishing on the inertia of the places of
  `cs(S)`" can **not** be applied to `ỹ`; the induction needs the one-dimensional case in the
  paper's shape ((H1), (H2) relative to the auxiliary level `Λ' = K̃` and the set `T'`).

**Already available** (all sorry-free, axiom-clean, in this workspace): the Chebotarev place
`Work.SSGRoute.exists_split_place_avoiding`; the local Kummer dictionary for every prime `p`
(`Work.SSGRoute.local_kummer_dictionary`, `Work.SSGRoute.local_kummer_dictionary_two`); Kummer
theory (`Work.AbsoluteKummer.kummerEquiv`, `NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`);
Grünwald over a number field (`Work.SSGRoute.grunwald_surjective_odd`,
`Work.SSGRoute.grunwald_surjective_two`); global class field theory
(`NK.CFTLib.artinReciprocityIdeal_proved`, `Work.SSGRoute.classField_exists_ramified`,
`NK.CFTLib.hilbertReciprocity_cyclic`); and the `μ_p` form of 1--5 (with the sharpened (b) and the
Frobenius/Chebotarev steps) as the sibling statements
`Work.SSGRoute.shafarevich_z_data_mup` / `_two` / `Work.SSGRoute.sw_z_exists_odd_sketch`.

-/

/-! ## Session-5 note: two further routes to this file's obligation

* `Submission/Work/SSGRoute/ZConstruction/ZDataLevelStep.lean`
  (`Work.SSGRoute.hasZData_sum_of_level_data`) proves the induction step of Schmidt--Wingberg §4
  (pp. 18--19) *in this vocabulary*: the sum `z₀ + z₁` has the `z`-data for `y₀ + y₁` whenever `z₀`
  has the data for `y₀` at `(Λ,S)` and vanishes on the Galois group of a level `N ⊇ Λ`, `z₁` has the
  data for the auxiliary class at the enlarged pair `(N,S')`, and the auxiliary class agrees with
  `y₁` on `cs(S)` and vanishes on `cs(S') ∖ cs(S)`.  This is the correctly stated replacement of the
  retracted confinement clauses (`Submission/Work/SSGRoute/z_data_mup_level.lean`).
* `Submission/Work/SSGRoute/ZConstruction/ZDataRealisation.lean`
  (`Work.SSGRoute.z_data_general_of_realisation`,
  `Work.SSGRoute.shafarevich_z_construction_of_realisation`) proves the conclusion of this file (and
  of the node) from the *single* arithmetic input `Work.SSGRoute.IsRealisationInput` of the sibling
  §4 development `Submission/Work/SSGRoute/ZSplit/`.

Consequently the obligation `Work.SSGRoute.z_data_general_of_ramified` below has exactly two kinds
of missing input, both shared with the rest of the project: the one-dimensional (`A = μ_p`)
statements (`Work.SSGRoute.z_data_mup_core`, `Work.SSGRoute.shafarevich_z_data_two`) and the
level-`K` Tate--Poitou realisation of §4 (`Work.SSGRoute.IsRealisationInput`, i.e. the Poitou--Tate
exactness for the local datum of a global class, which the level-`K` layer
`Submission/Work/SSGRoute/ZSplit/levelK_*.lean` is building -- see `ZSplit/LEVELK_STATUS.md`). -/

/-! ## The cocycle form of the `z`-data

The `z`-data statements of the sibling nodes (`Work.SSGRoute.shafarevich_z_data_mup`,
`Work.SSGRoute.shafarevich_z_data_two`, `Work.SSGRoute.sw_z_exists_odd_sketch`) state their first
conjunct as `SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z` rather than as additivity
of `z` on `G_K`.  On `G_K` the action of `Gal(K/k)` is trivial, so the two formulations are
equivalent; the conversion is recorded here so that those statements can be plugged into
`Work.SSGRoute.z_data_general` (and hence into `Work.SSGRoute.shafarevich_z_construction`)
mechanically. -/

section CocycleForm

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [Normal k K]
  {E : Type} [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]

/-- On the fixing subgroup of `K`, where the action is trivial, the crossed-homomorphism condition
is additivity. -/
lemma isCocycleOn_fixingSubgroup_iff_additive (z : (Ω ≃ₐ[k] Ω) → E) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ↔
      ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h := by
  constructor
  · intro hcoc g hg h hh
    have h1 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
      exact hg
    rw [hcoc g hg h hh, h1, one_smul]
  · intro hadd g hg h hh
    have h1 : SSGRoute.res k K g = 1 := by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
      exact hg
    rw [h1, one_smul]
    exact hadd g hg h hh

end CocycleForm

/-! ## The one-dimensional gate `Work.SSGRoute.IsMupZData` from the two `μ_p` cores

`Work.SSGRoute.ZMupGate` (`Work.SSGRoute.isMupZData_of_odd`, `_of_two`, `_of_workspace`) performs
this packaging, but it sits *above* this file in the import DAG (it imports it), so the wrappers are
repeated here in the form (and under the names) this file needs.  The only difference from the two
cores `Work.SSGRoute.z_data_mup_core` (odd `p`) and `Work.SSGRoute.shafarevich_z_data_two`
(`p = 2`) is the conversion of "additive on `G_K`" into the `1`-cocycle identity for the trivial
action of `G_K` on the coefficients (`isCocycleOn_fixingSubgroup_iff_additive`). -/

section MupFromCores

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [Fintype (K ≃ₐ[k] K)]

/-- The odd-`p` one-dimensional gate from the odd `μ_p` core `Work.SSGRoute.z_data_mup_core`. -/
theorem isMupZData_of_core_odd (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    IsMupZData p k Ω K := by
  intro E _instE _instMod _instAct _instSMC _instFin h1 Λ _instΛf _instΛg hKΛ S hSfin hSdisj
    hSram y hy hyc hyS hyT hy0 hyinf
  obtain ⟨z, hcoc, hloc, h3, h4, h5, h6⟩ :=
    z_data_mup_core p hp k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y hy hyc hyS hyT hy0
      hyinf
  exact ⟨z, (isCocycleOn_fixingSubgroup_iff_additive z).mp hcoc, hloc, h3, h4, h5, h6⟩

/-- The `p = 2` one-dimensional gate from the `μ₂` core `Work.SSGRoute.shafarevich_z_data_two`. -/
theorem isMupZData_of_core_two (hp2 : p = 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    IsMupZData p k Ω K := by
  intro E _instE _instMod _instAct _instSMC _instFin h1 Λ _instΛf _instΛg hKΛ S hSfin hSdisj
    hSram y hy hyc hyS hyT hy0 hyinf
  obtain ⟨z, hcoc, hloc, h3, h4, h5, h6⟩ :=
    shafarevich_z_data_two p hp2 k Ω K Λ hKΛ ζ hζ hζK E h1 S hSfin hSdisj hSram y hy hyc hyS hyT
      hy0 hyinf
  exact ⟨z, (isCocycleOn_fixingSubgroup_iff_additive z).mp hcoc, hloc, h3, h4, h5, h6⟩

/-- The one-dimensional gate at every `p`, from the two `μ_p` cores. -/
theorem isMupZData_of_cores (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) :
    IsMupZData p k Ω K := by
  by_cases hp2 : p = 2
  · exact isMupZData_of_core_two hp2 ζ hζ hζK
  · exact isMupZData_of_core_odd hp2 ζ hζ hζK

end MupFromCores
/-! ## Reduction of the obligation to the ramified case

The obligation `z_data_general` splits: if `y` is already unramified at *every* place outside
`cs(S)` --- which is stronger than the hypotheses `hyS`, `hyT`, since it also forbids ramification
at the places outside `cs(S)` that *are* split in `Λ` --- then the candidate `z := y` (extended by
`0` off `G_K`) satisfies the whole `z`-data and the hard clause (b) is vacuous.  The genuine content
is therefore `Work.SSGRoute.z_data_general_of_ramified`: the case in which `y` *is* ramified at
some place outside `cs(S)` (necessarily split in `Λ`, by `hyS`), where Schmidt--Wingberg move the
ramification of `y` onto new primes carrying cyclic local components.
-/

/-- **The `z`-data in the unramified case**: if `y` vanishes on the inertia of every place outside
`cs(S)`, then `z := y` (extended by `0` off `G_K`) witnesses the `z`-data, and the sharpened
condition (b) is vacuous. -/
theorem z_data_general_of_unramified (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hunram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  classical
  refine ⟨fun σ => if σ ∈ K.fixingSubgroup then y σ else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    have hgh : g * h ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg hh
    simp only [if_pos hg, if_pos hh, if_pos hgh, hy g hg h hh]
  · obtain ⟨U, hUopen, hUc⟩ := hyc
    refine ⟨U, hUopen, fun g hg u hu huK => ?_⟩
    have hgu : g * u ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem hg huK
    simp only [if_pos hg, if_pos hgu, hUc g hg u hu huK]
  · intro B hB hconj σ hσK hσd
    simp only [if_pos hσK]
  · intro c hc hc2
    simp only [if_pos hc, hyinf c hc hc2]
  · intro B hB hnotconj hsplit σ hσK hσI
    simp only [if_pos hσK, hyS B hB hnotconj hsplit σ hσK hσI]
  · intro B hB hnotconj hsplit htrig
    obtain ⟨σ, hσI, hσK, hσne⟩ := htrig
    have hz : (if σ ∈ K.fixingSubgroup then y σ else 0) = 0 := by
      simp only [if_pos hσK, hunram B hB hnotconj σ hσK hσI]
    exact absurd hz hσne

/-- **The odd-`p` half of the ramified case, from the odd `μ_p` core.**

This is `Work.SSGRoute.z_data_general_of_ramified` (`ZConstruction/ZDataFinal.lean`) at odd `p`, in
the same shape (so that the file above can use it without ever mentioning `IsMupZData`): the
one-dimensional gate is supplied internally by `isMupZData_of_core_odd`, i.e. by the odd `μ_p` core
`Work.SSGRoute.z_data_mup_core`, and the auxiliary class by the Grünwald-with-escape realisation
`Work.SSGRoute.zDataGeneralOfMupAndZeta` (whose only extra hypothesis `hKimag` is a function out of
the empty type `p = 2`, hence vacuous here). -/
theorem z_data_general_of_ramified_of_core_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k Λ B →
        (∃ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        (∃ g ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
          ∀ δ ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
            z δ ∈ AddSubgroup.zmultiples (z g)) ∧
        (∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)) := by
  obtain ⟨z, hz⟩ := zDataGeneralOfMupAndZeta p k Ω K ζ hζ hζK (fun h2 => absurd h2 hp)
    (isMupZData_of_core_odd hp ζ hζ hζK) E Λ hKΛ S hSfin hSdisj hSram y hy hyc hyS hyT hy0 hyinf
  exact ⟨z, hz⟩

/-- **The ramified case of the `z`-data from the two gates** (the gate-level form of
`Work.SSGRoute.z_data_general_of_ramified`, *verified* to be the exact instantiation).

This is `Work.SSGRoute.z_data_general_of_mup_and_aux` (`ZConstruction/ZDataAux.lean`) with the raw
hypotheses of the node's statements packaged into `Work.SSGRoute.ZAmbient` and `Work.SSGRoute.ZHyp`.
It records, in a form the compiler checks, that

* the ambient hypotheses of `Work.SSGRoute.z_data_general_of_ramified` (`hKΛ`, `ζ`, `hζ`, `hζK`,
  `hSfin`, `hSdisj`, `hSram`) are *exactly* the fields of `Work.SSGRoute.ZAmbient` — in particular no
  condition of the target is unused or missing — and
* its six conditions on the datum `y` are *exactly* the fields of `Work.SSGRoute.ZHyp`.

Consequently, once the two gates are available (`Work.SSGRoute.MupGate` from the two arithmetic cores
by `Work.SSGRoute.mupGate_of_cores`, `ZConstruction/MupGate.lean`, and `Work.SSGRoute.AuxExists` from
`Work.SSGRoute.AuxPairingGate` together with the p. 18 realisation by
`Work.SSGRoute.auxExists_of_pairing_and_realisation` /
`Work.SSGRoute.auxExists_of_pairing_and_realisation_odd`, `ZConstruction/AuxAssembly.lean`), this is
the gate-level form of `Work.SSGRoute.z_data_general_of_ramified` (which, since session 34, is
proved in `ZConstruction/ZDataFinal.lean` by the orthogonality route, so this gate form is now
*redundant*: it is kept as the interface of the Poitou--Tate route). -/
theorem z_data_general_of_ramified_of_gates (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hmup : MupGate (p := p) K) (haux : AuxExists (p := p) K Λ S) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z :=
  z_data_general_of_mup_and_aux (p := p)
    ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ hmup haux E y
    ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩

open Work.SSGRoute.ZConstruction in
/-- **The odd-`p` case of the node's `z`-data from the one-dimensional gate ALONE** (no
`AuxExists`, no Poitou--Tate input).

`Work.SSGRoute.zDataGeneralOfMupAndZeta` proves the general coefficient module from the
one-dimensional gate `IsMupZData` together with the Grünwald-with-escape realisation, whose only
extra hypothesis is `hKimag : p = 2 → ∀ c ∈ K.fixingGroup, c ^ 2 = 1 → c = 1` -- **vacuous for odd
`p`** (it is a function whose domain `p = 2` is empty).  Hence for `p ≠ 2` the entire arithmetic
obligation of the `z`-data is the one-dimensional gate, i.e. the odd-`p` μ_p core
(`Work.SSGRoute.z_data_mup_core`, through `Work.SSGRoute.isMupZData_of_odd`): the auxiliary class
of the induction of Schmidt--Wingberg §4 is supplied by the Grünwald-with-escape realisation rather
than by the pairing/Poitou--Tate input `AuxExists`.  The statement is `ZAmbient`/`ZHyp`-shaped, so it
plugs directly into `Work.SSGRoute.z_data_general_of_ramified_of_gates`'s interface.

At `p = 2` the hypothesis `hKimag` is *false* in the node's setting (Ω is algebraically closed, so
`G_K` has involutions), so this route does not apply there: the prime-`2` case still needs the
`AuxExists` route (or a correction-aware variant of the Grünwald realisation). -/
theorem z_data_general_of_ramified_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)} (hAmb : ZAmbient (p := p) K Λ S)
    (hμ : IsMupZData p k Ω K) :
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  intro E _instE _instM _instF y hy
  -- the Galois action on the coefficients is irrelevant to the `z`-data: use the trivial one (the
  -- statement of `zDataGeneralOfMupAndZeta` carries the two action instances, the `ZAmbient`/`ZHyp`
  -- interface does not)
  letI : DistribMulAction (K ≃ₐ[k] K) E :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E := ⟨fun _ _ _ => rfl⟩
  obtain ⟨z, hz⟩ := zDataGeneralOfMupAndZeta p k Ω K hAmb.ζ hAmb.hζ hAmb.hζK
    (fun h2 => absurd h2 hp) hμ E Λ hAmb.hKΛ S hAmb.hSfin hAmb.hSdisj hAmb.hSram y
    hy.add hy.locconst hy.hyS hy.hyT hy.hy0 hy.hyinf
  exact ⟨z, hz⟩

/-- **The odd-`p` case of the `z`-data from the four gates, uniformly in `(Λ,S)`.**

This is `Work.SSGRoute.z_data_general_of_ramified` (and hence, through
`Work.SSGRoute.z_data_general`, the conclusion of the node
`Work.SSGRoute.shafarevich_z_construction`) for odd `p`, reduced to four *named* statements and
nothing else:

* `Work.SSGRoute.MupGate (p := p) K` -- the one-dimensional gate (the two μ_p cores);
* `Work.SSGRoute.AuxPairingGate (p := p) K` -- the level-`K` local Tate system with the product
  formula and the unramified orthogonality;
* `AuxDatumOrthogonalityGate (p := p) (K := K) Λ` -- for **every** auxiliary field `Λ`, the p. 18
  orthogonality of the prescribed datum `Work.SSGRoute.auxDatum K S ν` against the *honest* dual
  family (see the module docstring of `ZConstruction/AuxExistsAssembly.lean` for the state of this
  gate: the *proved* chase supplies only the relaxed family);
* `AuxDatumCounting (p := p) (K := K) Λ` -- for every `Λ`, the level-`K` Poitou--Tate counting
  inequality at a place set covering the places above `p` and the places ramified in the auxiliary
  level (without that coverage the inequality is false, see
  `ZDataMup/TATEPOITOU_STATUS.md`, "SESSION 4").

The auxiliary-class obligation `Work.SSGRoute.AuxExists` is supplied here by the assembly
`Work.SSGRoute.ZConstruction.auxExists_of_countingBlocks`
(`ZConstruction/AuxExistsAssembly.lean`), whose side hypotheses `hp : p ≠ 2`, `ζ`, `hζ`, `hζK` and
the coverage of `S` are exactly the fields of `Work.SSGRoute.ZAmbient`.  This is why the statement
below is *not* available for `p = 2`: there the involution clause of the realised class is the
archimedean condition of Shafarevich's prime-`2` correction, and it is not a consequence of the
argument `eq_one_of_mul_self_eq_one_of_fixes_primitiveRoot`. -/
theorem z_data_general_of_odd_gates (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hp : p ≠ 2) (hmup : MupGate (p := p) K)
    (hP : AuxPairingGate (p := p) K)
    (hgate : ∀ (Λ : IntermediateField k Ω),
      ZConstruction.AuxDatumOrthogonalityGate (p := p) (K := K) (Λ := Λ))
    (hcount : ∀ (Λ : IntermediateField k Ω),
      ZConstruction.AuxDatumCounting (p := p) (K := K) (Λ := Λ)) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF y hy
  exact z_data_general_of_mup_and_aux (p := p) hAmb hmup
    (Work.SSGRoute.ZConstruction.auxExists_of_countingBlocks (p := p) hp hAmb.hζ hAmb.hζK
      hAmb.hSfin hAmb.hSram hP (hgate Λ) (hcount Λ)) E y hy

/-- **The `z`-data from the one-dimensional gate and the auxiliary realisation at ANY `p`** —
including `p = 2`, where the auxiliary realisation must supply the involutions clause of the
realised class itself (the prime-`2` correction), which is exactly what
`Work.SSGRoute.ZConstruction.AuxRealisationGate` records with the false `hKimag` hypothesis removed.

This is the `ZAmbient`/`ZHyp`-shaped form of
`Work.SSGRoute.ZDataGen.zDataGeneralOfMupAndZetaGen`; at odd `p` the gate is supplied by
`Work.SSGRoute.ZConstruction.auxRealisationGate_odd`, and at `p = 2` it is the (still missing)
two-field narrow realisation — see `ACTION_p2_twoFieldRealisation.md`. -/
theorem z_data_general_of_realisationGate (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hreal : ZConstruction.AuxRealisationGate (p := p) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK))
    (hμ : IsMupZData p k Ω K) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  intro Λ _instΛf _instΛg S hAmb E _instE _instM _instF y hy
  -- the `z`-data of `HasZData` does not see the action of `Gal(K|k)` on the coefficients: use the
  -- trivial one when the ambient statement does not carry an action (as in
  -- `Work.SSGRoute.z_data_general_of_ramified_odd`)
  letI : DistribMulAction (K ≃ₐ[k] K) E :=
    { smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p) E := ⟨fun _ _ _ => rfl⟩
  obtain ⟨z, hz⟩ := ZDataGen.zDataGeneralOfMupAndZetaGen p k Ω K ζ hζ hζK hreal hμ E Λ hAmb.hKΛ
    S hAmb.hSfin hAmb.hSdisj hAmb.hSram y hy.add hy.locconst hy.hyS hy.hyT hy.hy0 hy.hyinf
  exact ⟨z, hz⟩

/-- **The whole `z`-data from the one-dimensional gate and the auxiliary realisation** (the raw
argument form of `Work.SSGRoute.z_data_general`, with the residual obligation `z_data_general_of_ramified`
replaced by the two named inputs).

This is the statement the node `Work.SSGRoute.shafarevich_z_construction` consumes through
`Work.SSGRoute.shafarevich_z_construction_of_zData`
(`ZConstruction/ZDataBridge.lean`): with the gate and `IsMupZData p k Ω K` supplied, the node
follows directly — for *every* `p`, including `p = 2` (where `Work.SSGRoute.ZDataMup.HistKummer`-style
`hKimag` hypotheses are false, and the gate `AuxRealisationGate` is the correct replacement). -/
theorem z_data_general_of_realisationGate_full (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ] [Fintype (K ≃ₐ[k] K)] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hreal : ZConstruction.AuxRealisationGate (p := p) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK))
    (hμ : IsMupZData p k Ω K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → E)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  classical
  by_cases hram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0
  · -- the ramified case: the one-dimensional gate and the auxiliary realisation
    obtain ⟨z, hz⟩ := z_data_general_of_realisationGate (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ)
      (hζ := hζ) (hζK := hζK) (hreal := hreal) (hμ := hμ) Λ S
      ⟨hKΛ, ζ, hζ, hζK, hSfin, hSdisj, hSram⟩ E y
      ⟨hy, hyc, hyS, hyT, hy0, hyinf⟩
    exact ⟨z, hz⟩
  · -- the unramified case
    refine z_data_general_of_unramified p k Ω K Λ hKΛ ζ hζ hζK E S hSfin hSdisj hSram y hy hyc
      hyS hyT hy0 hyinf ?_
    intro B hB hconj σ hσK hσI
    by_contra hne
    exact hram ⟨B, hB, hconj, σ, hσK, hσI, hne⟩


end Work.SSGRoute
