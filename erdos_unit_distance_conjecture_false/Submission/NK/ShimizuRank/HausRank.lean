import Submission.NK.ShimizuRank.Basic

/-!
# `NK.Reconstruct.HausRankInput` from two sharper residuals

`NK.Reconstruct.HausRankInput Ω ℓ` asserts the equality of the two models of the torsion-free
ℓ-adic abelianisation `Γ_K`,

  `rank_{ℤ_ℓ} (Γ_K ⧸ invisible) = r_ℓ(K) = rank_{ℤ_ℓ} (Γ_K ⧸ torsion)`,

for every number field `K` and every Galois extension `K' / K`.

This file decomposes it into the two ingredients that the *rank calculus* actually uses, and
proves the decomposition:

* `NK.ShimizuRank.GammaTFRankFinite Ω ℓ` — the rank `rank_{ℤ_ℓ} Γ_K^{tf}` is finite, i.e.
  `Module.rank` and `Module.finrank` agree on `Γ_K^{tf}`.  This is the first half of CoNF
  (10.3.20) (`Γ_K` is a finitely generated `ℤ_ℓ`-module).  Without it, `rankGamma` — being
  `Cardinal.toNat` of `Module.rank` — would be `0` on an infinite rank, so that
  `NK.Reconstruct.HausRankInput` is *strictly stronger* than the naive reading.

* `NK.ShimizuRank.InvisibleSubgroupTorsion Ω ℓ` — the invisible subgroup of `Γ_K` is a torsion
  group.  This is the genuine ℓ-adic group theory of `G_K^{ab,(ℓ)}`: `Γ_K` has the shape
  `ℤ_ℓ^{r} ⊕ T` with `T` torsion visible to no continuous character.

## The rank calculus

For any `ℤ_ℓ`-module `A` and submodule `N`, `rank A = rank (A ⧸ N) + rank N`
(`Submodule.rank_quotient_add_rank`).  Applying this to `N = invisibleSubmodule` and to
`N = GammaTorsion` for `A = Additive (Γ_K)`, and using that a torsion module has rank `0`
(`Module.IsTorsion.rank_eq_zero`):

  `rank (HausQuot) + rank (invisible) = rank (Γ_K)`,  `rank (Γ_K^{tf}) + rank (torsion) = rank (Γ_K)`.

Since both `invisible` and `torsion` are torsion, both drop out, giving `rank (HausQuot) =
rank (Γ_K^{tf})`, and `GammaTFRankFinite` converts the latter into `(r_ℓ(K) : Cardinal)`.

The converse is `hausRankInput_iff`: `HausRankInput` implies `GammaTFRankFinite` (a finite rank has
`toNat` equal to itself) and `InvisibleSubgroupTorsion`, because
`rank (invisible) + r_ℓ(K) = rank (Γ_K) = r_ℓ(K)` with all three cardinals finite, and cardinals can
be cancelled on the left by a finite cardinal (`Cardinal.add_le_add_iff_of_lt_aleph0`).  So the
reduction is *lossless*; the arithmetic content is concentrated in `InvisibleSubgroupTorsion`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.ShimizuRank

open NK.Reconstruct

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## Elementary rank lemmas -/

/-- **The rank of a torsion module vanishes.** -/
theorem rank_eq_zero_of_isTorsion {R : Type*} [Semiring R] [Nontrivial R] {M : Type*}
    [AddCommMonoid M] [Module R M] (h : Module.IsTorsion R M) : Module.rank R M = 0 :=
  Module.IsTorsion.rank_eq_zero h

/-- **The torsion submodule of `Γ_K` is a torsion module** (the instance is not provided for
`Submodule.torsion`, so the elementary proof is recorded here). -/
theorem isTorsion_gammaTorsion {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime] :
    Module.IsTorsion (PadicInt ℓ) ↥(GammaTorsion (K := K) (K' := K') ℓ) := by
  intro x
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (R := PadicInt ℓ)
    ((x : Additive (Gamma K K' ℓ)))).mp x.2
  exact ⟨a, Subtype.ext ha⟩

/-- **`Γ_K^{tf}` has finite rank**, i.e. `Module.finrank` and `Module.rank` agree there.  This is
`GammaTFRankFinite` at a single `K`, `K'`, and it is what converts `rankGamma` (a natural number,
`Cardinal.toNat` of the rank) into a genuine cardinal identity. -/
theorem rank_gammaTF_eq_finrank {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) < Cardinal.aleph0) :
    ((rankGamma K K' ℓ : ℕ) : Cardinal)
      = Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) := by
  rw [show rankGamma K K' ℓ
      = Module.finrank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) from rfl, Module.finrank,
    Cardinal.cast_toNat_eq_iff_lt_aleph0]
  exact h

/-- **The rank identity for the two quotients of `Γ_K`.**  For any number field `K`, any Galois
extension `K' / K` and any prime `ℓ`: if the invisible subgroup of `Γ_K` is torsion then

  `rank (Γ_K ⧸ invisible) = rank (Γ_K ⧸ torsion)`.

This is the whole formal content of `HausRankInput`: the torsion subgroup is torsion by
definition, so both quotients have the rank of `Γ_K`. -/
theorem rank_hausQuot_eq_rank_gammaTF {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (hT : Module.IsTorsion (PadicInt ℓ) ↥(invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ))) :
    Module.rank (PadicInt ℓ) (HausQuot K K' ℓ)
      = Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) := by
  have h1 := Submodule.rank_quotient_add_rank
    (invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ))
  have h2 := Submodule.rank_quotient_add_rank (GammaTorsion (K := K) (K' := K') (ℓ := ℓ))
  have h0 : Module.rank (PadicInt ℓ) ↥(invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)) = 0 :=
    rank_eq_zero_of_isTorsion hT
  have h0' : Module.rank (PadicInt ℓ) ↥(GammaTorsion (K := K) (K' := K') (ℓ := ℓ)) = 0 :=
    rank_eq_zero_of_isTorsion (isTorsion_gammaTorsion (K := K) (K' := K') (ℓ := ℓ))
  rw [h0, add_zero] at h1
  rw [h0', add_zero] at h2
  exact h1.trans h2.symm

/-! ## The truncation warning for `rankGamma`

`NK.Reconstruct.rankGamma K K' ℓ` is `Module.finrank (PadicInt ℓ) (GammaTF K K' ℓ)`, and
`Module.finrank` is `Cardinal.toNat ∘ Module.rank`; `Cardinal.toNat` sends every infinite cardinal to
`0`.  Consequently `rankGamma` *vanishes* as soon as the rank of `Γ_K^{tf}` is infinite, and in
particular it has no unconditional lower bound: the statement `1 ≤ rankGamma K K' ℓ` is *equivalent*
to `1 ≤ Module.rank (Γ_K^{tf}) < ℵ₀`.  This is why `GammaTFRankFinite` (the first half of CoNF
(10.3.20)) is an indispensable input, and it is the content of the finding reported in the README. -/

/-- **`rankGamma` is `0` when the rank of `Γ_K^{tf}` is infinite** (`Cardinal.toNat` truncates). -/
theorem rankGamma_eq_zero_of_aleph0_le {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : Cardinal.aleph0 ≤ Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)) :
    rankGamma K K' ℓ = 0 := by
  rw [show rankGamma K K' ℓ
      = Module.finrank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) from rfl, Module.finrank,
    Cardinal.toNat_eq_zero]
  exact Or.inr h

/-- **A nonzero value of `rankGamma` forces the rank to be finite** — the converse of
`rankGamma_eq_zero_of_aleph0_le`.  This is the sharp reason why `rankGamma` cannot be given an
unconditional lower bound. -/
theorem rank_lt_aleph0_of_rankGamma_ne_zero {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : rankGamma K K' ℓ ≠ 0) :
    Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) < Cardinal.aleph0 := by
  by_contra hlt
  rw [not_lt] at hlt
  exact h (rankGamma_eq_zero_of_aleph0_le hlt)

/-! ## `GammaTFRankFinite` from the pre-existing input `RankFormulaInput`

`NK.Reconstruct.RankFormulaInput K K' ℓ δ` (`Submission/Work/Reconstruct/torsionFreeGamma.lean`)
is the chapter's existing name for CoNF (10.3.20); its `finite` field is
`Module.Finite (PadicInt ℓ) (GammaTF K K' ℓ)`.  Since the rank of a finitely generated module is
finite (`Module.rank_lt_aleph0`), this gives the residual `GammaTFRankFinite` — so the residual is
*implied by* the input already on disk, and no new mathematics is hidden in it.  The `formula` and
`bound` fields of `RankFormulaInput` are not needed for this. -/

/-- **`GammaTFRankFinite` from finiteness of `Γ_K^{tf}` as a `ℤ_ℓ`-module.** -/
theorem gammaTFRankFinite_of_moduleFinite {ℓ : ℕ} [Fact ℓ.Prime]
    (h : ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
      [IsGalois K K'], Module.Finite (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)) :
    GammaTFRankFinite Ω ℓ :=
  fun K _ _ K' _ _ _ => Module.rank_lt_aleph0 (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ)

/-- **`GammaTFRankFinite` from `NK.Reconstruct.RankFormulaInput`**: the finiteness half of CoNF
(10.3.20) as it is already named in `Submission/Work/Reconstruct/torsionFreeGamma.lean`. -/
theorem gammaTFRankFinite_of_rankFormulaInput {ℓ : ℕ} [Fact ℓ.Prime]
    (h : ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
      [IsGalois K K'], ∃ δ : ℕ, RankFormulaInput K K' ℓ δ) :
    GammaTFRankFinite Ω ℓ :=
  gammaTFRankFinite_of_moduleFinite fun K _ _ K' _ _ _ => (h K K').choose_spec.finite

/-! ## The unconditional containment `torsion ⊆ invisible`

The invisible subgroup is the intersection of the kernels of all continuous characters
`Γ_K → ℤ_ℓ`.  A torsion element is killed by every such character, because a character is additive
and `ℤ_ℓ` has no zero divisors (`a * g x = g (a • x) = 0` with `a ≠ 0`).  Hence

  `GammaTorsion ⊆ invisibleSubmodule`

**unconditionally**.  This is the elementary half of the identification of the two models of
`Γ_K`: it gives, with no hypothesis at all, that `HausQuot` is a *quotient* of `Γ_K^{tf}`, hence

  `rank (Γ_K ⧸ invisible) ≤ rank (Γ_K ⧸ torsion)`;

the input `InvisibleSubgroupTorsion` is precisely the reverse inequality. -/

/-- **The torsion subgroup of `Γ_K` is contained in the invisible subgroup** (unconditional).

For `x` with `a • x = 0`, `a ≠ 0`, and any continuous character `g`:
`a * g x = g (a • x) = 0`, and `a ≠ 0` in the domain `ℤ_ℓ` forces `g x = 0`. -/
theorem gammaTorsion_le_invisibleSubmodule {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime] :
    GammaTorsion (K := K) (K' := K') ℓ ≤ invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ) := by
  intro x hx
  rw [mem_invisibleSubmodule_iff]
  intro g
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (R := PadicInt ℓ) x).mp hx
  have h1 : (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ) ((a : PadicInt ℓ) • x) = 0 := by
    rw [show (a : PadicInt ℓ) • x = a • x from rfl, ha, map_zero]
  rw [dual_apply_smul (g := (g : Additive (Gamma K K' ℓ) →+ PadicInt ℓ)) g.2
    (a : PadicInt ℓ) x] at h1
  exact (mul_eq_zero.mp h1).resolve_left (mem_nonZeroDivisors_iff_ne_zero.mp a.2)

/-- **The canonical surjection `Γ_K^{tf} ↠ HausQuot K K' ℓ`** (unconditional): `hausMk` kills the
torsion subgroup (`gammaTorsion_le_invisibleSubmodule`), hence descends to `Γ_K ⧸ torsion`. -/
noncomputable def gammaTFToHausQuot {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] :
    GammaTF (K := K) (K' := K') ℓ →ₗ[PadicInt ℓ] HausQuot K K' ℓ :=
  Submodule.liftQ (GammaTorsion (K := K) (K' := K') ℓ)
    (hausMk (K := K) (K' := K') (ℓ := ℓ)) (by
      intro x hx
      rw [LinearMap.mem_ker]
      exact (hausMk_eq_zero_iff x).mpr (gammaTorsion_le_invisibleSubmodule hx))

@[simp] theorem gammaTFToHausQuot_mk {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (x : Additive (Gamma K K' ℓ)) :
    gammaTFToHausQuot (K := K) (K' := K') ℓ (Submodule.Quotient.mk x)
      = hausMk (K := K) (K' := K') (ℓ := ℓ) x := by
  rw [gammaTFToHausQuot, Submodule.liftQ_apply]

/-- **The canonical surjection is surjective** (unconditional). -/
theorem gammaTFToHausQuot_surjective {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime] :
    Function.Surjective (gammaTFToHausQuot (K := K) (K' := K') ℓ) := by
  intro y
  obtain ⟨x, rfl⟩ := hausMk_surjective (K := K) (K' := K') (ℓ := ℓ) y
  exact ⟨Submodule.Quotient.mk x, by rw [gammaTFToHausQuot_mk]⟩

/-- **`HausQuot` is a quotient of `Γ_K^{tf}`** (unconditional), so its rank is at most `r_ℓ(K)`:
the surjection `hausMk` kills the torsion subgroup, hence descends to `Γ_K ⧸ torsion`. -/
theorem rank_hausQuot_le_rank_gammaTF {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime] :
    Module.rank (PadicInt ℓ) (HausQuot K K' ℓ)
      ≤ Module.rank (PadicInt ℓ) (GammaTF (K := K) (K' := K') ℓ) :=
  LinearMap.rank_le_of_surjective _ gammaTFToHausQuot_surjective

/-- **`InvisibleSubgroupTorsion` is the equality `invisible = torsion`.**

Since `torsion ⊆ invisible` holds unconditionally (`gammaTorsion_le_invisibleSubmodule`), the
predicate `InvisibleSubgroupTorsion` (the invisible subgroup *is* a torsion group) is equivalent to
the equality of the two submodules

  `invisibleSubmodule K K' ℓ = GammaTorsion K K' ℓ`.

This is the cleanest form of the residual: by `hausRankInput_iff_of_finite`,
`HausRankInput Ω ℓ` is equivalent to `GammaTFRankFinite Ω ℓ` together with this equality, i.e. to
"`Γ_K` is a finitely generated `ℤ_ℓ`-module and its `ℤ_ℓ`-torsion is exactly the subgroup invisible
to every continuous character". -/
theorem invisibleSubgroupTorsion_iff_eq_torsion {ℓ : ℕ} [Fact ℓ.Prime] :
    InvisibleSubgroupTorsion Ω ℓ ↔
      ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
        [IsGalois K K'],
        invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)
          = GammaTorsion (K := K) (K' := K') (ℓ := ℓ) := by
  constructor
  · intro h K _ _ K' _ _ _
    refine le_antisymm ?_ gammaTorsion_le_invisibleSubmodule
    intro x hx
    rw [Submodule.mem_torsion_iff]
    obtain ⟨a, ha⟩ := h K K' (x := ⟨x, hx⟩)
    exact ⟨a, congrArg Subtype.val ha⟩
  · intro h K _ _ K' _ _ _
    intro x
    have hmem : (x : Additive (Gamma K K' ℓ))
        ∈ GammaTorsion (K := K) (K' := K') (ℓ := ℓ) := by
      rw [← h K K']
      exact x.2
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (R := PadicInt ℓ)
      (x : Additive (Gamma K K' ℓ))).mp hmem
    exact ⟨a, Subtype.ext ha⟩

/-- **The kernel of the canonical surjection `Γ_K^{tf} ↠ HausQuot K K' ℓ`** is the image of the
invisible subgroup: a class `mk x` is killed iff `x` is invisible. -/
theorem gammaTFToHausQuot_mk_eq_zero_iff {K : Type*} [Field K] [NumberField K] {K' : Type*}
    [Field K'] [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime]
    (x : Additive (Gamma K K' ℓ)) :
    gammaTFToHausQuot (K := K) (K' := K') ℓ (Submodule.Quotient.mk x) = 0
      ↔ x ∈ invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ) := by
  rw [gammaTFToHausQuot_mk, hausMk_eq_zero_iff]

/-- **`InvisibleSubgroupTorsion` is exactly the injectivity of the canonical surjection
`Γ_K^{tf} ↠ HausQuot K K' ℓ`.**

This is the sharpest form of the residual: it says that the *torsion-free* quotient `Γ_K ⧸ torsion`
of Shimizu's `Γ_K` and the *Hausdorff* quotient `Γ_K ⧸ invisible` — which are always related by a
surjection (`gammaTFToHausQuot`, `rank_hausQuot_le_rank_gammaTF`) — are in fact the same group, so
that `Γ_K` has the shape `ℤ_ℓ^{r} ⊕ T` with the torsion `T` visible to no continuous character. -/
theorem invisibleSubgroupTorsion_iff_ker_eq_bot {ℓ : ℕ} [Fact ℓ.Prime] :
    InvisibleSubgroupTorsion Ω ℓ ↔
      ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
        [IsGalois K K'],
        LinearMap.ker (gammaTFToHausQuot (K := K) (K' := K') ℓ) = ⊥ := by
  constructor
  · intro h K _ _ K' _ _ _
    have heq := (invisibleSubgroupTorsion_iff_eq_torsion).mp h K K'
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨y, rfl⟩ :=
      Submodule.mkQ_surjective (GammaTorsion (K := K) (K' := K') ℓ) x
    rw [show Submodule.mkQ (GammaTorsion (K := K) (K' := K') ℓ) y
        = Submodule.Quotient.mk y from rfl, gammaTFToHausQuot_mk_eq_zero_iff] at hx
    have hy : y ∈ GammaTorsion (K := K) (K' := K') ℓ := by
      rw [← heq]
      exact hx
    exact (Submodule.Quotient.mk_eq_zero (GammaTorsion (K := K) (K' := K') ℓ)).mpr hy
  · intro h K _ _ K' _ _ _
    intro x
    have hker := h K K'
    have hx : gammaTFToHausQuot (K := K) (K' := K') ℓ
        (Submodule.Quotient.mk (x : Additive (Gamma K K' ℓ))) = 0 := by
      rw [gammaTFToHausQuot_mk_eq_zero_iff]
      exact x.2
    have hmem : Submodule.Quotient.mk (x : Additive (Gamma K K' ℓ))
        ∈ LinearMap.ker (gammaTFToHausQuot (K := K) (K' := K') ℓ) := by
      rw [LinearMap.mem_ker]
      exact hx
    rw [hker, Submodule.mem_bot] at hmem
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff (R := PadicInt ℓ)
      (x : Additive (Gamma K K' ℓ))).mp
      ((Submodule.Quotient.mk_eq_zero (GammaTorsion (K := K) (K' := K') ℓ)).mp hmem)
    exact ⟨a, Subtype.ext ha⟩

/-- **Under `InvisibleSubgroupTorsion` the two models of `Γ_K` are isomorphic**: the canonical
surjection `Γ_K^{tf} ↠ HausQuot K K' ℓ` is a `ℤ_ℓ`-linear isomorphism. -/
theorem gammaTF_linearEquiv_hausQuot {ℓ : ℕ} [Fact ℓ.Prime] (h : InvisibleSubgroupTorsion Ω ℓ)
    (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'] :
    Nonempty (GammaTF (K := K) (K' := K') ℓ ≃ₗ[PadicInt ℓ] HausQuot K K' ℓ) := by
  have hker := (invisibleSubgroupTorsion_iff_ker_eq_bot).mp h K K'
  have hinj : Function.Injective (gammaTFToHausQuot (K := K) (K' := K') ℓ) := by
    rw [← LinearMap.ker_eq_bot]
    exact hker
  exact ⟨LinearEquiv.ofBijective _ ⟨hinj, gammaTFToHausQuot_surjective⟩⟩

/-! ## The reduction -/

/-- **`HausRankInput` from the two residuals.**  The invisible subgroup being torsion makes the two
models of `Γ_K` have equal rank, and finiteness of the rank identifies that common rank with
`r_ℓ(K)`. -/
theorem hausRankInput_of_residual {ℓ : ℕ} [Fact ℓ.Prime]
    (hT : InvisibleSubgroupTorsion Ω ℓ) (hF : GammaTFRankFinite Ω ℓ) : HausRankInput Ω ℓ := by
  intro K _ _ K' _ _ _
  rw [rank_gammaTF_eq_finrank (hF K K')]
  exact rank_hausQuot_eq_rank_gammaTF (hT K K')

/-! ## The converse: nothing is lost (modulo finiteness of the rank)

The two directions below show that, *given* `GammaTFRankFinite`, the single statement
`HausRankInput` is exactly the statement `invisible ⊇` ... `= torsion`.  One has to be careful
with one point: `rankGamma` is `Cardinal.toNat` of `Module.rank (Γ_K^{tf})`, so on a module of
*infinite* rank `rankGamma` is `0` and `HausRankInput` degenerates to "`HausQuot` is torsion";
`HausRankInput` therefore does *not* by itself force `Γ_K^{tf}` to have finite rank.  The
finiteness input of CoNF (10.3.20) must be carried separately — see the discussion in the module
docstring of `Basic.lean` and the final report. -/

/-- **`HausRankInput` implies that the invisible subgroup has rank `0`**, given that the rank of
`Γ_K^{tf}` is finite.

The rank of `Γ_K` is the sum of the ranks of the invisible subgroup and of `HausQuot`
(`Submodule.rank_quotient_add_rank`), and also the sum of the ranks of the torsion subgroup
(which is `0`) and of `Γ_K^{tf}`; with `HausRankInput` and finiteness both sums equal `r_ℓ(K)`.
Cancelling the finite cardinal `r_ℓ(K)` (`Cardinal.add_le_add_iff_of_lt_aleph0`) gives
`rank (invisible) = 0`, which over the domain `ℤ_ℓ` is equivalent to torsion-ness
(`rank_eq_zero_iff`). -/
theorem rank_invisibleSubmodule_eq_zero_of_residual {ℓ : ℕ} [Fact ℓ.Prime]
    (hF : GammaTFRankFinite Ω ℓ) (h : HausRankInput Ω ℓ)
    (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'] :
    Module.rank (PadicInt ℓ) ↥(invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)) = 0 := by
  have hfin := hF K K'
  have h1 := Submodule.rank_quotient_add_rank
    (invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ))
  have h2 := Submodule.rank_quotient_add_rank (GammaTorsion (K := K) (K' := K') (ℓ := ℓ))
  have h0' : Module.rank (PadicInt ℓ) ↥(GammaTorsion (K := K) (K' := K') (ℓ := ℓ)) = 0 :=
    rank_eq_zero_of_isTorsion (isTorsion_gammaTorsion (K := K) (K' := K') (ℓ := ℓ))
  rw [h0', add_zero] at h2
  rw [← rank_gammaTF_eq_finrank hfin] at h2
  rw [h K K'] at h1
  rw [← h2] at h1
  -- h1 : ↑(rankGamma K K' ℓ) + rank (invisible) = ↑(rankGamma K K' ℓ)
  have hle : Module.rank (PadicInt ℓ) ↥(invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)) ≤ 0 :=
    (Cardinal.add_le_add_iff_of_lt_aleph0
      (α := Module.rank (PadicInt ℓ) ↥(invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ)))
      (β := 0) (γ := ((rankGamma K K' ℓ : ℕ) : Cardinal)) Cardinal.natCast_lt_aleph0).mp (by
        rw [zero_add, add_comm]
        exact le_of_eq h1)
  exact le_antisymm hle zero_le

/-- **`HausRankInput` implies that the invisible subgroup is torsion** — the converse of
`rank_hausQuot_eq_rank_gammaTF`, modulo the finiteness input. -/
theorem invisibleSubgroupTorsion_of_hausRankInput {ℓ : ℕ} [Fact ℓ.Prime]
    (hF : GammaTFRankFinite Ω ℓ) (h : HausRankInput Ω ℓ) : InvisibleSubgroupTorsion Ω ℓ := by
  intro K _ _ K' _ _ _
  have hz := rank_invisibleSubmodule_eq_zero_of_residual hF h K K'
  rw [rank_eq_zero_iff] at hz
  intro x
  obtain ⟨a, ha, hax⟩ := hz x
  exact ⟨⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha⟩, Subtype.ext (congrArg Subtype.val hax)⟩

/-- **The exact decomposition of `HausRankInput`, modulo finiteness of the rank.**

Given the rank-finiteness input of CoNF (10.3.20), the identification of the two models of `Γ_K`
is *equivalent* to the sharp statement that the invisible subgroup is exactly the torsion
subgroup. -/
theorem hausRankInput_iff_of_finite {ℓ : ℕ} [Fact ℓ.Prime] (hF : GammaTFRankFinite Ω ℓ) :
    HausRankInput Ω ℓ ↔ InvisibleSubgroupTorsion Ω ℓ :=
  ⟨fun h => invisibleSubgroupTorsion_of_hausRankInput hF h,
    fun h => hausRankInput_of_residual h hF⟩

end NK.ShimizuRank
