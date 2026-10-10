import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `z`-data and `ytilde`-realisation vocabulary of Schmidt–Wingberg §4

This module holds the predicate `IsZData` (Schmidt–Wingberg’s `z`-data for an exposed witness)
and the predicate `IsYRealisation` (the `ytilde`-deliverable of §4, pp. 18–19) together with the
companion lemmas that read off their clauses.  They are the shared vocabulary of the `ZSplit` and
`ZConstruction` lanes.

**Why this module exists (import placement).**  These predicates were originally declared inside
`Submission/Work/SSGRoute/shafarevich_theorem13.lean` (the node `Work.SSGRoute.shafarevich_theorem13`),
which put every file that consumed them *above* the node and hence made them unusable for the
node’s own proof: the Z-route of `_NOTE_STEP4_DESIGN.md` §3 (`z_realisation_of_grunwald`, then
`z_data_general_of_ramified`) must live *below* the node.  They are moved here, below the node,
verbatim, and the node’s file imports this module, so no consumer changes except that imports may
be re-pointed at this module directly.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-- **Schmidt–Wingberg's `z`-data for a given witness `z` and datum `y`** (the conclusion of
`Work.SSGRoute.z_data_general` with the witness exposed). -/
def IsZData (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K Λ : IntermediateField k Ω) {E : Type} [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (S : Finset (ValuationSubring Ω)) (y z : (Ω ≃ₐ[k] Ω) → E) : Prop :=
  (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
  IsLocConstOn K.fixingSubgroup z ∧
  (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → z σ = y σ) ∧
  (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
  (∀ B : ValuationSubring Ω, IsFinPlace k B →
    (∀ A ∈ S, ¬ IsConjPlace k A B) → ¬ IsSplitIn k Λ B →
    ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → z σ = 0) ∧
  (∀ B : ValuationSubring Ω, IsFinPlace k B →
    (∀ A ∈ S, ¬ IsConjPlace k A B) → IsSplitIn k Λ B →
    (∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
    (∃ g ∈ decomp k B ⊓ K.fixingSubgroup,
      ∀ δ ∈ decomp k B ⊓ K.fixingSubgroup, z δ ∈ AddSubgroup.zmultiples (z g)) ∧
    (∀ Q : ValuationSubring Ω, IsConjPlace k B Q →
      (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
      ∀ τ ∈ decomp k Q ⊓ K.fixingSubgroup, z τ = 0))

/-- **The `⊕`-combination of two `z`-data with disjoint ramification.**

If `zE` and `zF` are `z`-data for the data `y` and `y'`, and at every place `B ∉ cs(S)` that is split
in `Λ` and at which one of the two is ramified the other one *vanishes* on the local group of every
`G_k`-conjugate of `B`, then the pair `(zE, zF)` is `z`-data for `(y, y')` in the product module.

This is the verification in Schmidt–Wingberg §4, pp. 18–19 (in the notation of the paper: for
`P ∈ T(K)` the two summands add up to `y_P`, for `P ∈ T_0 ∖ T(K)` the `μ_p`-summand vanishes, so the
sum inherits the sharpened cyclicity from the summand that is ramified there).  Note that only the
last clause needs the disjointness; the other five are read off clause-by-clause. -/
theorem IsZData.prod (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K Λ : IntermediateField k Ω) {E F : Type} [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    [AddCommGroup F] [Module (ZMod p) F]
    [DistribMulAction (K ≃ₐ[k] K) F] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) F]
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → E) (y' : (Ω ≃ₐ[k] Ω) → F)
    (zE : (Ω ≃ₐ[k] Ω) → E) (zF : (Ω ≃ₐ[k] Ω) → F)
    (hE : IsZData p K Λ S y zE) (hF : IsZData p K Λ S y' zF)
    (hdisj : ∀ B : ValuationSubring Ω, IsFinPlace k B →
      (∀ A ∈ S, ¬ IsConjPlace k A B) → IsSplitIn k Λ B →
      ((∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ zE σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, IsConjPlace k B Q →
          ∀ τ ∈ decomp k Q ⊓ K.fixingSubgroup, zF τ = 0) ∧
      ((∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ zF σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, IsConjPlace k B Q →
          ∀ τ ∈ decomp k Q ⊓ K.fixingSubgroup, zE τ = 0)) :
    IsZData p K Λ S (fun δ => (y δ, y' δ)) (fun δ => (zE δ, zF δ)) := by
  obtain ⟨hE1, hE2, hE3, hE4, hE5, hE6⟩ := hE
  obtain ⟨hF1, hF2, hF3, hF4, hF5, hF6⟩ := hF
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) additivity of the pair
    intro g hg h hh
    simp only [Prod.mk_add_mk, Prod.smul_mk]
    rw [hE1 g hg h hh, hF1 g hg h hh]
  · -- (2) local constancy of the pair
    obtain ⟨U, hU, hcU⟩ := hE2
    obtain ⟨V, hV, hcV⟩ := hF2
    refine ⟨U ⊓ V, hU.inter hV, fun g hg u hu hgu => ?_⟩
    have huU : u ∈ U := (Subgroup.mem_inf.mp hu).1
    have huV : u ∈ V := (Subgroup.mem_inf.mp hu).2
    simp only []
    rw [hcU g hg u huU hgu, hcV g hg u huV hgu]
  · -- (3) agreement with the pair datum at the places of `cs(S)`
    intro B hB hconj σ hσG hσ
    simp only []
    rw [hE3 B hB hconj σ hσG hσ, hF3 B hB hconj σ hσG hσ]
  · -- (4) involutions
    intro c hc hc2
    simp only []
    rw [hE4 c hc hc2, hF4 c hc hc2]
    rfl
  · -- (5) vanishing on the outside inertia
    intro B hB hconj hnotsplit σ hσG hσI
    simp only []
    rw [hE5 B hB hconj hnotsplit σ hσG hσI, hF5 B hB hconj hnotsplit σ hσG hσI]
    rfl
  · -- (6) the sharpened condition (b) for the pair
    intro B hB hconj hsplit hram
    obtain ⟨σ, hσI, hσG, hσne⟩ := hram
    simp only [] at hσne
    have hpair : zE σ ≠ 0 ∨ zF σ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hσne (Prod.ext h.1 h.2)
    rcases hpair with hEram | hFram
    · -- the first summand is ramified at `B`: the second one vanishes on all conjugates
      have hramE : ∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ zE σ ≠ 0 :=
        ⟨σ, hσI, hσG, hEram⟩
      have hzeroF := (hdisj B hB hconj hsplit).1 hramE
      obtain ⟨hcyc, hconjv⟩ := hE6 B hB hconj hsplit hramE
      refine ⟨?_, ?_⟩
      · -- cyclicity: the pair takes values in the multiples of one pair
        obtain ⟨g, hg, hgz⟩ := hcyc
        refine ⟨g, hg, fun δ hδ => ?_⟩
        obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgz δ hδ)
        refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
        have hgB : zF g = 0 := hzeroF B ⟨1, one_smul _ B⟩ g hg
        have hdB : zF δ = 0 := hzeroF B ⟨1, one_smul _ B⟩ δ hδ
        simp only [Prod.smul_mk]
        rw [hm, hgB, hdB]
        simp
      · -- the pair vanishes on the local groups of the other conjugates
        intro Q hconjQ hnotQ τ hτ
        simp only []
        rw [hconjv Q hconjQ hnotQ τ hτ, hzeroF Q hconjQ τ hτ]
        rfl
    · -- the second summand is ramified at `B`: symmetric
      have hramF : ∃ σ, IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ zF σ ≠ 0 :=
        ⟨σ, hσI, hσG, hFram⟩
      have hzeroE := (hdisj B hB hconj hsplit).2 hramF
      obtain ⟨hcyc, hconjv⟩ := hF6 B hB hconj hsplit hramF
      refine ⟨?_, ?_⟩
      · obtain ⟨g, hg, hgz⟩ := hcyc
        refine ⟨g, hg, fun δ hδ => ?_⟩
        obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp (hgz δ hδ)
        refine AddSubgroup.mem_zmultiples_iff.mpr ⟨m, ?_⟩
        have hgB : zE g = 0 := hzeroE B ⟨1, one_smul _ B⟩ g hg
        have hdB : zE δ = 0 := hzeroE B ⟨1, one_smul _ B⟩ δ hδ
        simp only [Prod.smul_mk]
        rw [hgB, hdB, hm]
        simp
      · intro Q hconjQ hnotQ τ hτ
        simp only []
        rw [hconjv Q hconjQ hnotQ τ hτ, hzeroE Q hconjQ τ hτ]
        rfl

/-!
STATUS (session of 2026-09-26, late).  One new proved lemma, and three mathematical findings that
close off routes; recorded so that the next session does not re-derive them.

**NEW (proved, axiom-clean).**  The realisation predicate `IsYRealisation` has been sharpened in the
two ways the induction of §4 needs (both matching the *paper's* data, and both matching the general
interface `Work.SSGRoute.PT.pt_selmer_relaxed`, whose local data is prescribed at the involutions
too):

* clause (3) (the prescribed local components) is now imposed at *every* conjugate of a place of `T`
  and not only at the representatives — this is what the paper does (`ỹ_P = y⁰⁰_P` for
  `P ∈ T(K)`), and it is unavoidable: for a cocycle on `G_K` the values on the local groups of two
  conjugate places of `k` are *unrelated* (the cocycle is only additive on `G_K`), so the
  representatives do not determine the conjugates.  New accessor: `IsYRealisation.locAgree_conj`.
* a new final conjunct: `ytilde` vanishes on the involutions of `G_K` (accessor
  `IsYRealisation.involutions`).  This is the fourth hypothesis (`hyinf`) of the one-dimensional
  `z`-statements; it is *not* implied by the other clauses (a coboundary on `⟨c⟩` need not vanish at
  `c`), so it has to be prescribed by the realisation — exactly as in `pt_selmer_relaxed`, whose
  local datum `β` lives on the involution subgroups.

On top of that, **`IsYRealisation.zStatementHypotheses`** proves that the class `ytilde` produced by
the realisation satisfies, *for the auxiliary level* `(Λ, S₀)`, the four vanishing hypotheses
(`hyS`-analogue, `hyT`-analogue, `hy0`-analogue and `hyinf`) under which the one-dimensional
`z`-statements are stated, as soon as the *prescribed* datum `f` carries the corresponding two
properties (which for `f = y⁰⁰`, the `μ_p`-component of the datum of Theorem 13, are exactly `hyT`
and `hy0` of `y`).  This is the interface bridge of the induction: it shows that the shape of the
hypotheses of the existing one-dimensional statements *is* the right one for the paper's induction,
because `ytilde` is unramified at `S₀ ∖ T` *by construction of the realisation* — the obstacle
recorded in `Work.SSGRoute.ZConstruction.ZDataGeneral` to the effect that the one-dimensional input
would have to be re-stated in the paper's shape `(H1)`,`(H2)` therefore does **not** apply to the
formalisation's statements: with `ytilde` from the realisation, the existing hypotheses are
satisfied.

**FINDING 1 (this file): the "Poitou–Tate only" route to Theorem 13 fails, and this is the
mathematical reason for the paper's §4 construction.**  One may hope to prove the theorem by
prescribing, at the finite set `T = S ∪ {involutions}`, the local datum `cor(y)|T` and appealing to
a Poitou–Tate realisation statement; the datum would then be orthogonal to every global class of
`E^∨(1)` unramified outside `T`, by *reciprocity* for the global class `cor(y)` plus the fact that
the contributions of the remaining places vanish (a class unramified at a place annihilates the
unramified subgroup there — hence the *unramified* places outside the ramification set contribute
nothing).  This works, and gives a solution `x` unramified outside `T`, **provided one prescribes the
datum `0` at the places where `cor(y)` is ramified outside `S` (the "bad" places).  Those places are
exactly the obstacles: by reciprocity the sum over `T` of the pairings equals minus the sum over the
bad places, and the latter does *not* vanish in general (a class that is unramified at a place need
not annihilate the ramified classes there — e.g. over `ℚ₂` the unramified class of `5` pairs
nontrivially with the ramified class of `2`: `(2,5)_2 = -1`).  The freedom of prescribing data at
*fresh* places (Chebotarev) is precisely what is used in the paper to make the total datum
orthogonal; there is no shortcut through Poitou–Tate alone.

**FINDING 2 (this file): the formalised hypotheses are *not* stronger than the paper's.**
`hSram` forces `S` to contain the places over `p` and the places ramified in `Λ`; `hyS` kills the
inertia at the places outside `S` that do not split in `Λ`, which is exactly what `y ∈ H¹(k_S|K,A)`
gives in the paper's setting (a place outside `cs(Λ|k) ∪ T` is unramified by that membership), and
`hyT` says `y` is unramified at the places of `S` — the paper's "`y_P` unramified for `P ∈ T(K)`".
So the statement is the paper's Theorem 13 and its truth is not in doubt; the gap is proof, not
statement.

**FINDING 3 (this file): for the general coefficient module the paper's induction does *not*
suffice, and this is the hard part of the node.**  The paper's induction step needs a *direct
summand* decomposition `A = A_0 ⊕ μ_p` (the decomposition `z = z⁰ + z⁰⁰` of the classes is taken
componentwise).  Hence their induction only reaches the modules that are direct sums of
one-dimensional modules and copies of `μ_p` — a proper class: e.g. `𝔽₂[ℤ/2] = 𝔽₂[ε]/ε²` is
indecomposable of dimension two with a unique one-dimensional submodule which is *not* a summand,
and it is not a summand of any direct sum of one-dimensional modules either, so no retraction
argument can reach it.  (`Work.SSGRoute.ZDataGeneral` states its theorem for *all* finite `E`, and
`Work.SSGRoute.solves_of_free` reduces the theorem for `E` to the theorem for the co-induced module
`𝔽_p[G] ⊗ E` — but by Shapiro's lemma that case is *equivalent* to the level-`K` statement with
coefficients in `E`, so it is not a reduction in difficulty either.)  The honest general statement
is therefore the §4 argument for a coefficient module `A` which is *its own Tate dual*
(`A ≅ A^∨(1)`, which the *free* module and `E ⊕ E^∨(1)` are, and which makes the local cup-product
pairing `A × A → μ_p` available where the paper uses the Hilbert symbol), together with the
retraction `Work.SSGRoute.shafarevich_z_statement_of_retract` (the statement for `E` follows from
the statement for `E ⊕ E^∨(1)`, since `E` is a summand).  That general-`A` §4 argument — the
one-dimensional statement with the local Kummer dictionary replaced by the general local Tate
pairing — is the remaining mathematical content of `z_data_general_of_ramified` for a general `E`.

**Available machinery for it** (proved, axiom-clean, in the workspace): the general local Tate
pairing and its reciprocity (`H1Pair/*`, `PT/*`, `E7Arch/*` — see the lanes' status reports), the
Poitou–Tate realisation in the sharp (unramified-outside) form (`PT.pt_selmer_relaxed`, one input
left), Chebotarev with the "new prime" conditions
(`Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split`), the local Kummer dictionary for every `p`
(`Work.SSGRoute.local_kummer_dictionary`, `_two`), the `p = 2` combinatorics
(`Work.SSGRoute.ZDataTwo.{two_partition,pigeonhole_three,three_term_cancellation}`), the two-term
pigeonhole (`Work.SSGRoute.pigeonhole_two_eq`), and the `⊕`-assembly of the `z`-data
(`Work.SSGRoute.HasZData.add`, `hasZData_add_of_split_confined`, `kills_decomp_of_split_of_vanishes`,
`Work.SSGRoute.IsZData.prod`).
-/

/-- **The `ytilde`-deliverable of Schmidt–Wingberg §4, pp. 18–19.**

In the induction step of Schmidt–Wingberg's Theorem 13 one replaces the pair `(Λ, T)` by
`(Λ₀, T₀) = (K̃Λ, T ∪ Ram(K̃|k))` (where `K̃` is the Galois closure over `k` of the field cut out by
the class `z⁰` for `A₀`) and needs a class `ytilde ∈ H¹(k_{S₀}|K, μ_p)` whose local components are the
prescribed data `f` at the places above `T` and *zero* at the places above `T₀ ∖ T`, and which is
unramified at every place of `k` outside `S₀` that is not split in the auxiliary field `Λ`.

This predicate is that deliverable, with the witness `ytilde` exposed.  Two points of *level* matter,
and both are forced (they were corrected after explicit computations; see the STATUS block at the end
of the file):

* `ytilde` is a class *over `K`*: it is an additive, locally constant function on
  `G_K = K.fixingSubgroup`, so its local component at a place `B` lives on the *level-`K` local group*
  `decomp k B ⊓ K.fixingSubgroup`.  On that group a coboundary is identically zero (the action of
  `G_K` on `ZMod p` is trivial), so `IsCoboundaryOn (res k K) (decomp k B ⊓ K.fixingSubgroup)
  (ytilde - f B)` says exactly that `ytilde` and `f B` have the same local component at `B` — which is
  the paper's "`ỹ_P = y⁰⁰_P`".  The datum `f B` is an arbitrary function on `G_k`; only its values on
  the level-`K` local group are seen.
* the ramification of `ytilde` is forbidden exactly where the *one-dimensional* statement for `ytilde`
  (applied at the auxiliary pair `(Λ, T₀)`) forbids it, namely at the places outside `S₀` that are not
  split in `Λ`; at the places outside `S₀` that *are* split in `Λ` the class `ytilde` may be ramified
  (those are precisely the places at which the sixth conjunct of the `z`-data takes over).  This
  weakening is *not* cosmetic: with `k = K = ℚ`, `p = 2`, `Λ = ℚ(√5)`, `T = S₀ = {2, 5, 13}` and
  `ν = χ₄₁` (the quadratic class of `41`), the datum realised by `ν` has no realisation which is
  unramified at *all* places outside `S₀`: such a realisation would be an element of `ℚ^×/ℚ^{×2}`
  divisible by no prime outside `{2,5,13}`, i.e. one of `±2ᵃ5ᵇ13ᶜ` with `a, b, c ∈ {0,1}`, whose local
  components must be trivial at `2` and at `5` (where `41 ≡ 1 mod 8`, `41 ≡ 1 mod 5`) and the
  unramified class of `2` at `13` (as `41 ≡ 2 mod 13`); the only candidates with the correct
  component at `13` are `±2` and `±5`, and these have the wrong component at `2` (`2 ∤` and
  `5 ∉ (ℚ₂^×)²`) and at `5` (`2` is a non-residue mod `5`, and `5` is ramified).  With the corrected
  conjunct, `ytilde := ν` itself is a realisation (it is ramified only at the split-in-`Λ` place
  `41`). -/
def IsYRealisation (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (Λ : IntermediateField k Ω) (T S₀ : Finset (ValuationSubring Ω))
    (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (ytilde : (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  IsCocycleOn (res k K) K.fixingSubgroup ytilde ∧
  IsLocConstOn K.fixingSubgroup ytilde ∧
  (∀ B : ValuationSubring Ω, (∃ A ∈ T, IsConjPlace k A B) →
    IsCoboundaryOn (res k K) (decomp k B ⊓ K.fixingSubgroup) (fun σ => ytilde σ - f B σ)) ∧
  (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S₀, IsConjPlace k A B) →
    (∀ A ∈ T, ¬ IsConjPlace k A B) →
    ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ytilde σ = 0) ∧
  (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S₀, ¬ IsConjPlace k A B) →
    ¬ IsSplitIn k Λ B →
    ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ytilde σ = 0) ∧
  (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ytilde c = 0)

/-- The prescribed local components at the places above `T`. -/
theorem IsYRealisation.locAgree (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde) (A : ValuationSubring Ω) (hA : A ∈ T) :
    IsCoboundaryOn (res k K) (decomp k A ⊓ K.fixingSubgroup) (fun σ => ytilde σ - f A σ) :=
  h.2.2.1 A ⟨A, hA, isConjPlace_refl A⟩

/-- The prescribed local components at every conjugate of a place of `T`. -/
theorem IsYRealisation.locAgree_conj (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde) {B : ValuationSubring Ω}
    (hB : ∃ A ∈ T, IsConjPlace k A B) :
    IsCoboundaryOn (res k K) (decomp k B ⊓ K.fixingSubgroup) (fun σ => ytilde σ - f B σ) :=
  h.2.2.1 B hB

/-- The involutions of `G_K` are killed. -/
theorem IsYRealisation.involutions (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde) {c : Ω ≃ₐ[k] Ω} (hc : c ∈ K.fixingSubgroup)
    (hc2 : c ^ 2 = 1) : ytilde c = 0 :=
  h.2.2.2.2.2 c hc hc2

/-- The vanishing at the places above `S₀ ∖ T`. -/
theorem IsYRealisation.vanishes_new (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde) {B : ValuationSubring Ω} (hB : IsFinPlace k B)
    (hBsupp : ∃ A ∈ S₀, IsConjPlace k A B) (hBnotT : ∀ A ∈ T, ¬ IsConjPlace k A B)
    {σ : Ω ≃ₐ[k] Ω} (hσG : σ ∈ K.fixingSubgroup) (hσD : σ ∈ decomp k B) : ytilde σ = 0 :=
  h.2.2.2.1 B hB hBsupp hBnotT σ hσG hσD

/-- The unramifiedness at the places outside `S₀` that are not split in `Λ`. -/
theorem IsYRealisation.unramified (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde) {B : ValuationSubring Ω} (hB : IsFinPlace k B)
    (hBnot : ∀ A ∈ S₀, ¬ IsConjPlace k A B) (hns : ¬ IsSplitIn k Λ B)
    {σ : Ω ≃ₐ[k] Ω} (hσG : σ ∈ K.fixingSubgroup)
    (hσI : IsInertia k B σ) : ytilde σ = 0 :=
  h.2.2.2.2.1 B hB hBnot hns σ hσG hσI

/-- **The auxiliary class `ytilde` satisfies the hypotheses of the one-dimensional `z`-statements.**

At the auxiliary level `(Λ, S₀)` the class `ytilde` produced by the Poitou–Tate realisation satisfies
the four vanishing hypotheses under which the one-dimensional (`A = μ_p`) existence theorems are
stated: unramifiedness outside `S₀`, unramifiedness at the places of `S₀`, the vanishing on the
local groups required at the places of `S₀`, and the vanishing on the involutions (the last one is
part of the realisation predicate itself).  The prescribed data `f` at the places above `T` has to
carry the corresponding properties (for `f = y⁰⁰`, the `μ_p`-component of the datum of Theorem 13,
these are exactly `hyT` and `hy0`).

This is the interface bridge of the induction of Schmidt--Wingberg §4: it is what lets the
one-dimensional statement be applied to `ytilde` (p. 18: "we can apply the induction hypothesis to
the field extensions `Λ₀|K|k`, the sets `T₀`, `S₀` and the module `A = μ_p`"), and it is the reason
why the *shape* of the hypotheses of the one-dimensional statements is the right one for the
induction: `ytilde` is unramified at the places of `S₀ ∖ T` by construction of the realisation. -/
theorem IsYRealisation.zStatementHypotheses (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k]
    [Field Ω] [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p} {ytilde : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde)
    (hfunr : ∀ B : ValuationSubring Ω, (∃ A ∈ T, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → f B σ = 0)
    (hvanish : ∀ B : ValuationSubring Ω, (∃ A ∈ T, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → f B σ = 0) :
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S₀, ¬ IsConjPlace k A B) →
      ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ytilde σ = 0) ∧
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S₀, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ytilde σ = 0) ∧
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S₀, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ytilde σ = 0) ∧
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ytilde c = 0) := by
  have hres : ∀ σ ∈ K.fixingSubgroup, res k K σ = 1 := by
    intro σ hσ
    rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker (K := k)]
    exact hσ
  refine ⟨?_, ?_, ?_, fun c hc hc2 => h.2.2.2.2.2 c hc hc2⟩
  · intro B hB hnotconj hnsplit σ hσG hσI
    exact h.2.2.2.2.1 B hB hnotconj hnsplit σ hσG hσI
  · intro B hB hconj σ hσG hσI
    by_cases hT : ∃ A ∈ T, IsConjPlace k A B
    · obtain ⟨m, hm⟩ := h.2.2.1 B hT
      have hσd : σ ∈ decomp k B := hσI.1
      have hval := hm σ ⟨hσd, hσG⟩
      change ytilde σ - f B σ = res k K σ • m - m at hval
      rw [hres σ hσG, one_smul, sub_self, sub_eq_zero] at hval
      rw [hval, hfunr B hT σ hσG hσI]
    · exact h.2.2.2.1 B hB hconj (fun A hA hc => hT ⟨A, hA, hc⟩) σ hσG hσI.1
  · intro B hB hconj hvanishB σ hσG hσd
    by_cases hT : ∃ A ∈ T, IsConjPlace k A B
    · obtain ⟨m, hm⟩ := h.2.2.1 B hT
      have hval := hm σ ⟨hσd, hσG⟩
      change ytilde σ - f B σ = res k K σ • m - m at hval
      rw [hres σ hσG, one_smul, sub_self, sub_eq_zero] at hval
      rw [hval, hvanish B hT hvanishB σ hσG hσd]
    · exact h.2.2.2.1 B hB hconj (fun A hA hc => hT ⟨A, hA, hc⟩) σ hσG hσd

/-- The deliverable is closed under addition of the data. -/
theorem IsYRealisation.add (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K Λ : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {T S₀ : Finset (ValuationSubring Ω)}
    {f f' : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p}
    {ytilde ytilde' : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : IsYRealisation p K Λ T S₀ f ytilde) (h' : IsYRealisation p K Λ T S₀ f' ytilde') :
    IsYRealisation p K Λ T S₀ (fun A σ => f A σ + f' A σ) (fun σ => ytilde σ + ytilde' σ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := h'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg hh hhh
    simp only [Pi.add_apply]
    rw [h1 g hg hh hhh, h1' g hg hh hhh, smul_add]
    abel
  · obtain ⟨U, hU, hcU⟩ := h2
    obtain ⟨U', hU', hcU'⟩ := h2'
    refine ⟨U ⊓ U', hU.inter hU', fun g hg u hu hgu => ?_⟩
    simp only [Pi.add_apply]
    rw [hcU g hg u ((Subgroup.mem_inf.mp hu).1) hgu, hcU' g hg u ((Subgroup.mem_inf.mp hu).2) hgu]
  · intro B hB
    obtain ⟨m, hm⟩ := h3 B hB
    obtain ⟨m', hm'⟩ := h3' B hB
    refine ⟨m + m', fun σ hσ => ?_⟩
    have hh := hm σ hσ
    have hh' := hm' σ hσ
    simp only [Pi.add_apply]
    rw [sub_eq_iff_eq_add] at hh hh' ⊢
    rw [hh, hh', smul_add]
    abel
  · intro B hB hsupp hnot σ hσG hσD
    simp only [Pi.add_apply]
    rw [h4 B hB hsupp hnot σ hσG hσD, h4' B hB hsupp hnot σ hσG hσD, add_zero]
  · intro B hB hnot hns σ hσG hσI
    simp only [Pi.add_apply]
    rw [h5 B hB hnot hns σ hσG hσI, h5' B hB hnot hns σ hσG hσI, add_zero]
  · intro c hc hc2
    simp only [Pi.add_apply]
    rw [h6 c hc hc2, h6' c hc hc2, add_zero]

open _root_.SSGRoute

/-- **The one-dimensional (`A = μ_p`) case of the `z`-data, at every pair `(Λ,S)`.** -/
def IsMupZData (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
    Module.finrank (ZMod p) E ≤ 1 →
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
    ∀ (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, IsFinPlace k A) →
    (∀ A ∈ S, ∀ B ∈ S, IsConjPlace k A B → A = B) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k Λ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, IsConjPlace k A B) →
    ∀ (y : (Ω ≃ₐ[k] Ω) → E),
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h) →
    IsLocConstOn K.fixingSubgroup y →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
      ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → y σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → y σ = 0) →
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) →
    ∃ z, IsZData p K Λ S y z

/-- **The auxiliary/realisation input of the paper's induction.**  For every datum `ν` on `G_K`
satisfying the vanishing conditions at `(Λ,S)` there are a datum `f` agreeing with `ν` at the places
of `S` (the extension of `ν|S` by zero at the new places of `T₀ ⊇ T`), a class `yt` realising `f`
(Schmidt--Wingberg's class of §4, pp. 18--19), and one-dimensional `z`-data `zF` for `yt` at the
auxiliary pair `(T₀,T₀)`. -/
def IsAuxiliaryZData (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
    ∀ (Λ₀ : IntermediateField k Ω) [FiniteDimensional k Λ₀] [IsGalois k Λ₀],
    Λ ≤ Λ₀ → K ≤ Λ₀ →
    ∀ (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L], L ≤ Λ₀ →
    ∀ (S₀ : Finset (ValuationSubring Ω)),
    (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L B →
      ∃ A ∈ S₀, IsConjPlace k A B) →
    (∀ A ∈ S₀, IsFinPlace k A) →
    (∀ A ∈ S₀, ∀ B ∈ S₀, IsConjPlace k A B → A = B) →
    ∀ (S : Finset (ValuationSubring Ω)),
    (∀ A ∈ S, IsFinPlace k A) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k Λ₀ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S₀, IsConjPlace k A B) →
    ∀ (ν : (Ω ≃ₐ[k] Ω) → ZMod p),
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, ν (g * h) = ν g + ν h) →
    IsLocConstOn K.fixingSubgroup ν →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
      ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ν σ = 0) →
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ν c = 0) →
    ∃ f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ A : ValuationSubring Ω, (∃ A' ∈ S, IsConjPlace k A' A) → f A = ν) ∧
      ∃ yt zF, IsYRealisation p K Λ₀ S S₀ f yt ∧ IsZData p K Λ₀ S₀ yt zF

/-- **The realisation input**: the local data of a global class `ν` on `G_K`, prescribed at a finite
set `S` of pairwise non-conjugate places (extended by zero at the new places of `T₀ ⊇ T`), is
realised by a class `ỹ`.  Its proof is the Poitou--Tate exactness in degree one applied to the
datum of the global class `ν` (Schmidt--Wingberg §4, the diagram chase at the bottom of p. 18). -/
def IsRealisationInput (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [Fintype (K ≃ₐ[k] K)] [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] : Prop :=
  ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ], K ≤ Λ →
    ∀ (Λ₀ : IntermediateField k Ω) [FiniteDimensional k Λ₀] [IsGalois k Λ₀],
    Λ ≤ Λ₀ → K ≤ Λ₀ →
    ∀ (L : IntermediateField k Ω) [FiniteDimensional k L] [Normal k L], L ≤ Λ₀ →
    ∀ (S₀ : Finset (ValuationSubring Ω)),
    (∀ B : ValuationSubring Ω, IsFinPlace k B → IsRamifiedIn k L B →
      ∃ A ∈ S₀, IsConjPlace k A B) →
    (∀ A ∈ S₀, IsFinPlace k A) →
    (∀ A ∈ S₀, ∀ B ∈ S₀, IsConjPlace k A B → A = B) →
    ∀ (S : Finset (ValuationSubring Ω)),
    (∀ A ∈ S, IsFinPlace k A) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B →
      (IsRamifiedIn k Λ₀ B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S₀, IsConjPlace k A B) →
    ∀ (ν : (Ω ≃ₐ[k] Ω) → ZMod p),
    (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, ν (g * h) = ν g + ν h) →
    IsLocConstOn K.fixingSubgroup ν →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∀ A ∈ S, ¬ IsConjPlace k A B) →
      ¬ IsSplitIn k Λ B → ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, IsInertia k B σ → ν σ = 0) →
    (∀ B : ValuationSubring Ω, IsFinPlace k B → (∃ A ∈ S, IsConjPlace k A B) →
      (¬ IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ decomp k B → ν σ = 0) →
    (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → ν c = 0) →
    ∃ f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ A : ValuationSubring Ω, (∃ A' ∈ S, IsConjPlace k A' A) → f A = ν) ∧
      ∃ yt, IsYRealisation p K Λ₀ S S₀ f yt

end Work.SSGRoute
