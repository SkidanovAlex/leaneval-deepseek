import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic core of Schmidt–Wingberg §4 (the `z`-construction, odd `p`)

This module isolates the **genuine arithmetic** that the lemma
`Work.SSGRoute.z_data_mup_core` consumes, in as primitive a form as is convenient: the existence
of the class `z` with Schmidt–Wingberg's sharpened condition (b), over an odd prime `p`, with
coefficients in the trivial `𝔽_p`-module `ZMod p`.

## Mathematical content

This is the `A = μ_p` case of the construction of `z ∈ H¹(k_S|K, A)` in the proof of Theorem 13 of

* A. Schmidt, K. Wingberg, *Šafarevič's theorem on solvable groups as Galois groups*,
  arXiv:math/9809211, §4, pp. 13–20,

with the **corrected trigger** of (b): the construction produces `z` which agrees with `y` at the
places of `S`, is unramified outside `S` up to one prime per conjugacy class of the new ramification,
and satisfies `z_P^σ = 0` for `σ ≠ 1` at every place `P` at which `z` is *ramified*.  In the
vocabulary of the project this is:

* `z` is additive on `G_K = K.fixingSubgroup` and locally constant there (a continuous `1`-cocycle
  for the trivial action on `ZMod p`);
* `z = y` on `D_B ⊓ G_K` for every finite place `B` conjugate to an element of `S`;
* `z` vanishes on the involutions of `G_K`;
* `z` vanishes on the inertia of every finite place `B ∉ cs(S)` that is not split in `N` (this is
  the freedom of *choosing the new ramification primes inside the split-in-`N` set*, available by
  Chebotarev);
* at every finite place `B ∉ cs(S)` that *is* split in `N` and at which `z` is ramified (i.e. `z` is
  non-zero on `I_B ⊓ G_K`), the class `z` vanishes on `D_Q ⊓ G_K` for every conjugate `Q` of `B`
  that is not a `G_K`-conjugate of `B` — Schmidt–Wingberg's `z_{σP} = 0` for `σ ≠ 1`.

## Status and proof route

Not proved here.  The proof is the argument of SW §4: the iterated construction
`z_1, z_2, … ∈ H¹(k_S|K, μ_p)` with the Tate–Poitou exact sequence (the two exact lines of the
diagram at the top of p. 14 of the paper: localisation `H¹(k_S|K, μ_p) → ∏_{T_n} H¹(K_P, μ_p) →
H¹(k_S|K, ℤ/p)^∨`), Chebotarev's density theorem (choice of the new prime `P_{n+1}` and of its
Frobenius), the pigeonhole principle (`Ψ_N(z_N) = Ψ_N(z_i)`), and the Hilbert-symbol product
formula (verification of `z^σ_P = 0` at `σ P_N`).

The available machinery is `NK.NUV2.chebotarev_all0` (Chebotarev over `ℚ`, with
`hFC := NK.CFTLib.fundamentalClassElement`), `NK.CFTLib.artinReciprocityIdeal_proved`,
`NK.NUV2.kernelCondition_all` (local reciprocity / local duality), the local Tate pairing
(`Work.SSGRoute.local_tate_duality*`), the Poitou–Tate/Selmer vocabulary
(`Work.SSGRoute.ShaCocycles`, `pt_localPairing`, `pt_selmer_relaxed`), and the Hilbert-symbol
product formula (`Work.HilbertSymbol.hilbertReciprocity_prod`).
## REVIEW LOG

* `Submission/Work/SSGRoute/ZDataMup/sw_z_exists_odd_sketch` (the `•`-free restatement of `sw_z_exists_odd_sketch`
  below): **both reviewers approved** ("looks correct as stated", "the genuine SW §4 existence
  statement").  Delegation was attempted repeatedly and refused each time with "The team is busy
  right now" — the fleet has been saturated throughout; the request stays filed for the next
  opening.
* `Submission/Work/SSGRoute/ZDataMup/tatePoitou_h1_realisation_sketch`: reviewer 1 found a genuine level
  mismatch — the dual Selmer group of the localisation at level `K` lives on `G_K`, not on `G_k`.
  **Fixed here**: in `tatePoitou_h1_realisation_sketch` both `hrec` and `horth` now quantify over
  `K.fixingSubgroup`-cocycles (and `horth`'s unramifiedness clause is likewise stated on
  `K.fixingSubgroup`), matching the level-`K` conclusion.  Any delegation of this piece must use
  the corrected statement.

* `Submission/Work/SSGRoute/ZDataMup/exists_localTateSystem_productFormula` (Piece 3), second round:
  after the self-duality (`ζ, hζ, hζK`) and level-`K` fixes, Reviewer 2 approved; Reviewer 1
  argued that the `T'`-disjointness and the unramifiedness clause must live at the *same* level as
  the vanishing clause.  The consistent resolution (applied to Pieces 1 and 3) is to put **both** at
  the level-`K` (`K.fixingSubgroup`-conjugacy) level: `T'` is one place per prime of `K` and `a, b`
  are unramified outside the `K.fixingSubgroup`-conjugates of `T'`, so the sum is the full level-`K`
  reciprocity sum over the primes of `K`.  (Dropping to `IsConjPlace k` instead would sum only the
  `k`-primes below `T'`, which is not the reciprocity sum for `μ_p` over `K`.)

* **Prelude warning (learned twice).** Statements sent to `request_review`/`request_lemma` are
  elaborated in a prelude without `open scoped Pointwise`, so `•` on `ValuationSubring` /
  `Submodule`-like objects fails to synthesize.  All delegation statements must use the unfolded
  membership form (`∀ x, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A`), bridged to the `•`-form by
  `conjPlace_eq_iff_mem` in `z_data_mup_core.lean`.

## STATUS (this node, and how the development fits together)

`Work.SSGRoute.z_data_mup_core` (file `z_data_mup_core.lean`) is **proved** except for the single
Theorem `sw_z_exists_odd_sketch` below, which it consumes in the case in which `y` is *ramified* somewhere
outside `cs(S)`; the complementary case (`y` unramified outside `cs(S)`) is proved there outright
with `z := y`, using `hyS`, `hyc`, `hyinf` and `h1` (the cyclicity half of the sixth conjunct comes
from `dim E ≤ 1`).

`sw_z_exists_odd_sketch` is the **hard case** of the arithmetic core: by `hyS`, a place outside `cs(S)` at
which `y` is ramified must be split in `N`, and this is exactly the situation of Schmidt–Wingberg
§4 in which the auxiliary class `z` is constructed by the Tate–Poitou/Chebotarev/Hilbert-symbol
argument (the "genuine new arithmetic" of `Submission/Work/SSGRoute/DESIGN.md`, sibling of
`shafarevich_z_data_mup`, `coker_obstruction`, `sha2_image_of_Hm2`).

A delegation request for the equivalent `•`-free statement at the path
`Submission/Work/SSGRoute/ZDataMup/sw_z_exists_odd_sketch` was reviewed and **approved by both reviewers**
as the intended SW §4 statement, but could not be handed to a prover: the team was fully occupied.
A proof of `sw_z_exists_odd_sketch` is the only missing piece of this development.

-/

open scoped Pointwise

namespace Work.SSGRoute


/-! ## Piece 1: the Tate–Poitou exactness in degree `1` (the SW §4 input)

The first of the four sub-lemmas into which the arithmetic core is cut.  It is the exactness of the
lower line of the diagram at the top of p. 14 of Schmidt–Wingberg §4:

  `H¹(k_S|K, μ_p) → ∏_{P ∈ S(K)} H¹(K_P, μ_p) → H¹(k_S|K, ℤ/p)^∨`,

read as a *realisation* statement: the local data at a finite set of primes is realised by a global
class which is unramified outside that set, as soon as it is orthogonal to the dual Selmer group —
the classes against which the local Tate pairings pair it.  The local Tate pairing family is taken
as a parameter (with its axioms as a hypothesis), exactly as in the workspace's
`Work.SSGRoute.pt_selmer_relaxed`, so that this piece is independent of the construction of the
pairing (that is `Work.SSGRoute.pt_localPairing`). -/

/-- The local Tate pairings on the trivial `𝔽_p[G_K]`-module `ZMod p`, one for each decomposition
group, with their local axioms: `𝔽_p`-bilinearity on local `1`-cocycles, vanishing on a coboundary
in either argument, and perfectness (left non-degeneracy) on cocycles modulo coboundaries. -/
structure IsLocalTateSystem (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
      ZMod p) : Prop where
  additive_left : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) →
      ∀ (a a' b : (Ω ≃ₐ[k] Ω) → ZMod p),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair H (a + a') b = pair H a b + pair H a' b
  additive_right : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) →
      ∀ (a b b' : (Ω ≃ₐ[k] Ω) → ZMod p),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
        pair H a (b + b') = pair H a b + pair H a b'
  vanishes_coboundary : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) →
      ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        (SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a ∨
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) →
        pair H a b = 0
  perfect : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)),
      (∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧ H = SSGRoute.decomp k A) →
      ∀ a : (Ω ≃ₐ[k] Ω) → ZMod p,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
          pair H a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a

/-- **Piece 1: the Tate–Poitou exactness in degree `1`, realisation form** (SW §4, the `A = μ_p`
case).  Given a family of local Tate pairings together with the global reciprocity law, a local
datum at a finite set `T` of pairwise non-conjugate finite places which is orthogonal (with respect
to the pairing) to every global cocycle which is unramified outside the conjugates of `T` is
realised by a global cocycle `z` which is unramified outside the conjugates of `T`. -/
theorem tatePoitou_h1_realisation_sketch
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p)
    (hpair : IsLocalTateSystem p k Ω K pair)
    (hrec : ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a →
      SSGRoute.IsLocConstOn K.fixingSubgroup a →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b →
      SSGRoute.IsLocConstOn K.fixingSubgroup b →
      ∀ (T' : Finset (ValuationSubring Ω)), (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
      (∀ A ∈ T', ∀ B ∈ T', SSGRoute.IsConjPlace k A B → A = B) →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
      ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a b = 0)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (f : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hf : ∀ A ∈ T, SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) (f A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp k A) (f A))
    (horth : ∀ b : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b →
      SSGRoute.IsLocConstOn K.fixingSubgroup b →
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → b σ = 0) →
      ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (f A) b = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup z ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A)
        (fun σ => z σ - f A σ)) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by sorry


/-! ## Pieces 2–4: Chebotarev, the symbol product formula, and the pigeonhole

The remaining three of the four sub-lemmas into which the arithmetic core is cut (the first being
`tatePoitou_h1_realisation_sketch` above).  Together with `IsLocalTateSystem` they are the inputs from
which the SW §4 construction of `sw_z_exists_odd_sketch` is assembled:

* **Piece 2 (`chebotarev_sameFrobeniusClass_split`)** chooses the new ramification prime
  `P_{n+1} ∈ S∖T_n(K)` with a prescribed Frobenius class, split in `N` — the step of SW §4 which
  fixes the local data of `z_{n+1}` at the new prime;
* **Piece 3 (`exists_localTateSystem_productFormula`)** produces the local Tate pairing system
  with its product formula (`∏_P (a,b)_P = 1` of the paper), i.e. the two duality inputs `hpair`,
  `hrec` of Piece 1;
* **Piece 4 (`pigeonhole_two_eq`, proved below)** is the shoe-box principle producing `i < N` with
  `Ψ_N(z_N) = Ψ_N(z_i)`. -/

/-- **Piece 2: the Chebotarev step of SW §4.**  Let `L, N` be finite Galois intermediate fields,
`T'` a finite set of pairwise non-conjugate finite places, and `τ` an element of `G_k` acting
trivially on `N`.  Then there is a finite place `B` outside the conjugates of `T'`, unramified in
`L`, split in `N`, whose Frobenius in `L/k` is the class of `τ`: some `σ ∈ decomp k B` restricts to
`res k L τ` on `L`.  This is Chebotarev's density theorem applied to the compositum `L·N` and the
conjugacy class of `res k (L·N) τ`; the requirement `res k N τ = 1` is exactly the compatibility of
"the prescribed `L/k`-Frobenius" with "split in `N`", which is how `sw_z_exists_odd_sketch` keeps its new
ramification primes inside the split-in-`N` set. -/
theorem chebotarev_frobenius_split_sketch (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω]
    (L N : IntermediateField k Ω) [FiniteDimensional k L] [IsGalois k L]
    [FiniteDimensional k N] [IsGalois k N]
    (T' : Finset (ValuationSubring Ω)) (hT'fin : ∀ B ∈ T', SSGRoute.IsFinPlace k B)
    (hT'disj : ∀ B ∈ T', ∀ C ∈ T', SSGRoute.IsConjPlace k B C → B = C)
    (τ : Ω ≃ₐ[k] Ω) (hτ : SSGRoute.res k N τ = 1) :
    ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ C ∈ T', ¬ SSGRoute.IsConjPlace k C B) ∧
      ¬ SSGRoute.IsRamifiedIn k L B ∧ SSGRoute.IsSplitIn k N B ∧
      ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k B ∧
        SSGRoute.res k L σ = SSGRoute.res k L τ := by sorry

/-- **Piece 3: the local Tate pairing system and its product formula** (SW §4; the Hilbert-symbol
product formula).  There is a family `pair` of local Tate pairings on the level-`K` cocycles
satisfying the local axioms `IsLocalTateSystem`, and for global cocycles `a, b` on `G_K` which are
unramified outside a finite set `T'` of places (one per prime of `k`), the sum of the local pairings
over `T'` vanishes — the exact two dualities (`hpair`, `hrec`) which
`tatePoitou_h1_realisation_sketch` consumes. -/
theorem exists_localTateSystem_productFormula
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] :
    ∃ pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p,
      IsLocalTateSystem p k Ω K pair ∧
      ∀ (a b : (Ω ≃ₐ[k] Ω) → ZMod p),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a →
        SSGRoute.IsLocConstOn K.fixingSubgroup a →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b →
        SSGRoute.IsLocConstOn K.fixingSubgroup b →
        ∀ (T' : Finset (ValuationSubring Ω)), (∀ A ∈ T', SSGRoute.IsFinPlace k A) →
        (∀ A ∈ T', ∀ B ∈ T', (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B) →
        (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) →
        ∑ A ∈ T', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a b = 0 := by sorry

/-- **Piece 4: the pigeonhole (`shoe box`) principle of SW §4.**  A sequence with values in a
finite set takes the same value at two distinct indices; applied to `a n = Ψ_n(z_n)` it produces
the pair `i < N` with `Ψ_N(z_N) = Ψ_N(z_i)`. -/
theorem pigeonhole_two_eq {ι : Type} [Fintype ι] (a : ℕ → ι) : ∃ i j : ℕ, i < j ∧ a i = a j := by
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun n : Fin (Fintype.card ι + 1) => a n) (by simp)
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with h | h
  · exact ⟨i.val, j.val, h, heq⟩
  · exact ⟨j.val, i.val, h, heq.symm⟩

/-- **Schmidt–Wingberg §4, odd `p`, `A = μ_p`: the existence of the class `z` with the sharpened
condition (b)**, with coefficients in the trivial `𝔽_p[G_K]`-module `ZMod p`.

Given a finite set `S` of pairwise non-conjugate finite places of `Ω` that contains the places of
`k` ramified in `N` and the places over `p`, and a class `y : G_k → ZMod p` additive and locally
constant on `G_K` which is unramified at the places of `cs(S)` (`hyT`), vanishes on the
decomposition groups of the places of `cs(S)` that are not split in `K` or lie over `p` (`hy0`),
vanishes on the involutions of `G_K` (`hyinf`), there is a class `z : G_k → ZMod p` with the same local behaviour
as `y` at the places of `cs(S)`, vanishing on the involutions, unramified at every place outside
`cs(S)` that is not split in `N`, and satisfying Schmidt–Wingberg's sharpened condition (b):
whenever `z` is ramified at a place `B ∉ cs(S)` split in `N`, `z` vanishes on the local group
`D_Q ⊓ G_K` of every conjugate `Q` of `B` that is not a `G_K`-conjugate of `B`. -/
theorem sw_z_exists_odd_sketch (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0) := by sorry

end Work.SSGRoute
