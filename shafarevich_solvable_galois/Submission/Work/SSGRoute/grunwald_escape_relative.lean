import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.GrunwaldEscapeCore.core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD 09-30: new Step-4 route (design: _NOTE_STEP4_DESIGN.md at the workspace root; read the section for your node). step4_yLarge_exists was FALSE (it asks for an everywhere-unramified y); Step4YPrescribed with the escape at D.Λ is right. Frattini argument for i ≥ 2 (N1), Grünwald with escape (N2, pairing-free; do NOT use kummerChar_eq_zero_iff_local_powClass, which has a sorry), the E-valued version (N3), local data (N4), and the (1,1) → (2,1) step via shafarevich_existence (N5). No Hochschild–Serre transgression and no Poitou–Tate input. Import sibling nodes you depend on (sorried until they land).
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-! ## Status note (session of the prover of this node): the skeleton, and the two things that are needed

**The statement is consistent (and true); do not "refute" it by a dimension count.**  A tempting
argument is: for a *fixed* escape place `Q`, the characters unramified outside `cs(T) ∪ cs(Q)` are
Kummer characters of elements `b ∈ Kˣ` whose divisors are supported on the primes of `T` and on the
prime of `K` below `Q` (mod `p`-th powers), i.e. (when `Cl(K) = 1`) classes of `S`-units, a group of
order `|O_S^×/O_S^{×p}| = (rank)·(μ_K/μ_K^p)`; e.g. `K = ℚ(ζ₃)`, `p = 3`, `T = {𝔭₃}`, `S = S_T ∪ {𝔮₀}`
gives `27`, while the local data space `Hom(G_{K_𝔭₃}, Z/3) = K_𝔭₃^×/(K_𝔭₃^×)³` has `81` elements,
so that a fixed `Q` cannot suffice.  That count is correct, but it does **not** contradict the
statement: in the conclusion `Q` is quantified **after** the datum, so the datum only has to lie in
the **union** over all split places `Q` of the images of the `S_Q`-unit classes — and the design's
Chebotarev step produces, for each datum, a *specific* `Q` (namely the one whose Frobenius in `M` is
`Art(𝔞)⁻¹`, where `𝔞` is the divisor of the Grünwald element `a₀`, which depends on the datum).
This is exactly why the statement needs `IsSplitIn k (L₁ ⊔ L₂) Q` and why the single escape place is
enough.

**The ramification criterion used throughout.**  For `p` prime, `μ_p ⊆ K`, `b ∈ Kˣ` and a finite
place `B` with `¬ B.valuation (p : Ω) < 1`:
`kummerCharZMod p hζ b` is unramified at `B` (vanishes on the inertia `I_B ∩ G_K`) if and only if
`p ∣ v_B(b)`.  Indeed, the character vanishes on the inertia iff `b ∈ (K_B^{un,×})^p ∩ K_B^×`; the
unramified extension's unit group `O_B^{un,×}` is `p`-divisible when `p ∤ B.valuation p` (its
principal units form a pro-`ℓ` group with `ℓ ≠ p`, and its Teichmüller part is the algebraically
closed residue unit group), so the condition is exactly `p ∣ v_B(b)`.  (The `p = 2` "unit" case of
this is on disk: `Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit`; the general `p` version is
the piece `SSGRoute/kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd`.)

**Skeleton of the proof (design steps 1–6, with the two refinements that were needed).**

1. `A ↦ (g + h A)|_{decomp A ⊓ G_K}` is additive (`hg`, `hh`) and vanishes on an open subgroup
   (`hgc` gives `g 1 = 0` and an open `U`, `hhc` the open subgroup for `h A`; intersect).  Grünwald
   then gives `z₀` realising the datum at `T`.  **Apply Grünwald at the base field `↥K` with top
   field `⊥`, not at `k`:** at that base `IsConjPlace ↥K A B = ∃ σ : Ω ≃ₐ[↥K] Ω, σ • A = B`, i.e.
   exactly the `G_K`-conjugacy of the statement's `hTdisj` (unfold `σ • A = B` with
   `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`), whereas at base `k` the theorems'
   `IsConjPlace k` is the stronger `G_k`-conjugacy, which `hTdisj` does not give.  Script:
   `IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩`;
   `NumberField ↥K := NumberField.of_module_finite k ↥K`;
   `hζK' : ζ ∈ (⊥ : IntermediateField ↥K Ω)` from `hζK` (`IntermediateField.mem_bot`);
   `IsFinPlace k A → IsFinPlace ↥K A` (`ValuationSubring.comap_comap`, `⊤.comap = ⊤`);
   datum `y ↦ g (φ y) + h A (φ y)`, `φ := (grunwaldSetupDecompEquiv k Ω K A).symm`, using
   `IntermediateField.fixingSubgroup_bot` to match `decomp ↥K A` with `decomp ↥K A ⊓ ⊤`;
   `hTdisj` → the `IsConjPlace ↥K` disjunct via `MulEquiv.symm_apply_apply` for
   `fixingSubgroupEquiv K` and `fixingSubgroupEquiv_mem_decomp`;
   continuity of the datum: `hgc` at `1` (with `hg` giving `g 1 = 0`) intersected with `hhc`'s open
   `U`, pushed through `isHomeomorph_decompEquiv`;
   output `z' : Ω ≃ₐ[↥K] Ω → ZMod p` transported along `IntermediateField.fixingSubgroupEquiv K` and
   extended by `0` off `K.fixingSubgroup`; `IsLocConstOn` via `krullTopology_mem_nhds_one_iff ↥K Ω`
   plus `IntermediateField.normalClosure`, `normalClosure.is_finiteDimensional`,
   `E.le_normalClosure` (a `k`-finite field containing a given `↥K`-finite one; avoids the missing
   `Module ↥K ↥E` instance).

### Verified ingredient for the `IsLocConstOn` finish (scratch file compiles; only the last inclusion is open)

The `k`-finite witness is `L := K ⊔ IntermediateField.adjoin k T`, where `T ⊆ Ω` is the image of a
finite generating set of `N` over `↥K`:

* `obtain ⟨t, htfin, ht⟩ : ∃ t : Set ↥N, t.Finite ∧ Algebra.adjoin ↥K t = ⊤` from
  `Subalgebra.fg_def.mp (Algebra.FiniteType.out (R := ↥K) (A := ↥N))` with
  `Algebra.FiniteType ↥K ↥N` by `inferInstance` (`Subalgebra.fg_def` yields a `Set` plus its
  `Finite` proof, *not* a `Finset`; `[Finite ↑t]` is `htfin.to_subtype`);
* `T := (↑) '' t`, `[Finite ↑T]` by `htfin.image _`; each `x ∈ T` is `IsIntegral k` by
  `isIntegral_trans (R := k) (A := ↥K) (y : Ω)
     ((IntermediateField.isIntegral_iff (S := N)).mp (Algebra.IsIntegral.isIntegral (R := ↥K) y))`
  with `Algebra.IsIntegral.of_finite k ↥K` and `Algebra.IsIntegral.of_finite ↥K ↥N`
  (`IsIntegral.tower_top` is the *wrong* direction);
* `FiniteDimensional k (IntermediateField.adjoin k T)` by
  `IntermediateField.finiteDimensional_adjoin hTint`, then `FiniteDimensional k L` by
  `IntermediateField.finiteDimensional_sup` — **no `S`/`FiniteType`-bridge for `↥K` is needed**, so
  the missing `Module ↥K ↥E` instance never appears;
* open step: `(N : Set Ω) ⊆ (L : Set Ω)`, from `ht` by `Algebra.adjoin_le_iff.mpr` applied to
  `(↑t : Set ↥N) ⊆ {y | (y : Ω) ∈ L}` (clear from `L ⊇ T` via `le_sup_right` +
  `IntermediateField.subset_adjoin`), the right-hand set being an `↥K`-subalgebra of `↥N` because
  `L` is a `k`-subfield containing `K` and `T`; then
  `krullTopology_mem_nhds_one_iff k Ω` at `L` with `L.fixingSubgroup ≤ fixSetSubgroup k Ω (N : Set Ω)`
  (immediate from `N ⊆ L`) and `Subgroup.isOpen_of_mem_nhds`.  The subgroup itself is
  `fixSetSubgroup k Ω S := {σ : G_k | ∀ x ∈ S, σ x = x}`, whose `inv_mem'` is discharged by
  `conv_lhs => rw [← ha x hx]; exact AlgEquiv.symm_apply_apply a x`.  This is in
  `Submission/Work/SSGRoute/_scratch_overK.lean`, which compiles.
2. Kummer theory turns `z₀` into `a₀ ∈ Kˣ` realising the datum at `T`
   (`Work.SSGRoute.exists_kummerChar_of_additive_locConst` is the `p = 2` case; the general `p`
   version follows the same route through `kummer_character_realization_inf`).
3. `𝔞` := the `T`-free part of `div(a₀)`, reduced mod `p`; `M` := the class field of
   `U := Kˣ·∏_{A∈T} K_A^{×p}·∏_{B∉T} O_B^×·𝕁^p` (an open subgroup, of exponent-`p` quotient;
   `Work.SSGRoute.classField_exists_ramified` is the existence theorem for open subgroups of prime
   index).  Its kernel on ideles is `U`, which gives: for a fractional ideal `𝔟` supported away from
   `T`, `Art_M(𝔟) = 1` iff `𝔟 = (c)·𝔡^p` with `c ∈ K_𝔭^{×p}` for every `𝔭 ∈ T`.
4. Orthogonality: `Art(𝔞)` is trivial on `M ∩ (L₁ ⊔ L₂)`.  For `L₁ = L₂ = K` this is automatic
   (`M ∩ K = K`); in general it is the reciprocity computation with `hgram`, `hTcov`, `horth₁`,
   `horth₂`.
5. Chebotarev: a place `Q`, split in `L₁ ⊔ L₂` and avoiding `T` (and `∞`), with `Frob_Q = Art(𝔞)⁻¹`
   in `M` — this is `Work.SSGRoute.ZDataTwo.chebotarev_frobenius_split` (proved, with
   `NK.Reconstruct.ChebotarevDensityInput` supplied by
   `NK.Reconstruct.chebotarevDensityInput_of_artinReciprocity`), applied with `L := M`,
   `N := L₁ ⊔ L₂` and `τ` an element with `res k N τ = 1` and `res k L τ = Art(𝔞)⁻¹`; the
   compatibility is step 4.
6. `Art(𝔞Q) = 1` in `Gal(M/K)`, so (step 3) `𝔞Q = (γ)·𝔡^p` with `γ ∈ K_𝔭^{×p}` for `𝔭 ∈ T`.
   Set `b := a₀/γ` (note: **divide**, not multiply — multiplying doubles the `𝔞`-part, which would
   leave `z` ramified at the primes dividing `𝔞`).  Then
   `div(b) = (T`-supported`)·Q⁻¹·(`p`-th powers`)`, so `b` is a local `p`-th power at `T` (hence
   `z := Kummer(b)` has the required local data at `T`) and, by the criterion above, `z` is
   unramified outside `cs(T) ∪ cs(Q)`.  Finally extend `z` from `G_K` to `G_k` by `0` outside `G_K`;
   additivity and local constancy on `G_K` are inherited, and all the clauses of the conclusion
   only test elements of `G_K`. -/

/-- Grünwald with escape (rank one, `μ_p ⊆ K`), in a pairing-free relative form.  This is the
arithmetic core shared by Step 4 and by the realisation input of Schmidt--Wingberg §4.

For `p = 2` the field `K` must have no real places (`hKimag`; this holds in every use, because
`μ₄ ⊆ K` there).  Data: a finite set `T` of finite places, one per prime of `K`, covering the places over `p` and
the places ramified in `L₁/K` or `L₂/K`; local additive functions `h A` on the level-`K` local groups;
and a global additive function `g` on `G_K` that is unramified outside `T`, except at places split
completely in `L₁`.  Prescribed local datum at `A ∈ T`: `g + h A`.

Orthogonality, stated per place with no local pairing:
* against characters of `Gal(L₁/K)`, the correction `h A` is zero, or every such character
  vanishes on the local group, or both `h A` and every such character are unramified at `A`;
* against characters of `Gal(L₂/K)`, the same trichotomy for the whole datum `g + h A`.

Conclusion: a global class `z` with the prescribed local data at `T`.  Outside `T`, `z` is ramified
at the `G_K`-conjugates of a single place `Q` at most, and `Q` splits completely in `L₁ ⊔ L₂`.

Proof route (no Poitou--Tate):
* Grünwald (`grunwald_surjective_odd` / `_two`) and Kummer theory give `a₀ ∈ Kˣ` with the local
  data at `T`.
* Global CFT: `classField_exists_ramified`, `artinReciprocityIdeal_proved`,
  `fundamentalClassElement`, `exists_artinIso_of_ideleArtin`. Let `M` be the maximal
  exponent-`p` abelian extension of `K` unramified outside `T`, i.e. the class field of
  `Kˣ·∏_T K_Aˣᵖ·∏_{B∉T} O_Bˣ·𝕁ᵖ`. The Artin symbol of the `T`-free divisor `𝔞` of `a₀` is
  trivial on `M ∩ (L₁ ⊔ L₂)`. This follows from reciprocity for `a₀` and for the Kummer element of
  `g`, together with the two orthogonality hypotheses.
* Chebotarev over `k` (the `t0Generation_cyclic` / `chebotarev_all0` machinery): there is a prime
  `Q` split in `L₁ ⊔ L₂` whose decomposition group in `M` is generated by `Art(𝔞)⁻¹`.
* Hence `𝔞·Q^u = (c)·𝔡ᵖ` with `c` a local `p`-th power at every place of `T`. Take `z` to be the
  Kummer character of `a₀·c`. -/
theorem grunwald_escape_relative (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (L₁ L₂ : IntermediateField k Ω) [FiniteDimensional k L₁] [IsGalois k L₁]
    [FiniteDimensional k L₂] [IsGalois k L₂] (hKL₁ : K ≤ L₁) (hKL₂ : K ≤ L₂)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, (∃ τ ∈ K.fixingSubgroup, τ • A = B) → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₁.fixingSubgroup) ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ L₂.fixingSubgroup)) →
      ∃ A ∈ T, ∃ τ ∈ K.fixingSubgroup, τ • A = B)
    (g : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hg : ∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, g (x * y) = g x + g y)
    (hgc : SSGRoute.IsLocConstOn K.fixingSubgroup g)
    (hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) → ¬ SSGRoute.IsSplitIn k L₁ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → g σ = 0)
    (h : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hh : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A (x * y) = h A x + h A y)
    (hhc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → h A x = 0)
    (horth₁ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₁.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0))
    (horth₂ : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, g σ + h A σ = 0) ∨
      (∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
        (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
        (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
        ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, χ σ = 0) ∨
      ((∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → g σ + h A σ = 0) ∧
        ∀ χ : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, χ (x * y) = χ x + χ y) →
          (∀ σ ∈ L₂.fixingSubgroup, χ σ = 0) →
          ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ → χ σ = 0)) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k (L₁ ⊔ L₂) Q ∧
      (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y ∈ K.fixingSubgroup, z (x * y) = z x + z y) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z σ = g σ + h A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ∀ τ ∈ K.fixingSubgroup, τ • A ≠ B) →
        (∀ τ ∈ K.fixingSubgroup, τ • Q ≠ B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  exact Work.SSGRoute.grunwald_escape_relative_smul_form p k Ω K ζ hζ hζK hKimag L₁ L₂ hKL₁ hKL₂
    T hTfin hTdisj hTcov g hg hgc hgram h hh hhc horth₁ horth₂

end Work.SSGRoute
