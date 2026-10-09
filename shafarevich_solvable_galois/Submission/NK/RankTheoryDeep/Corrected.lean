import Submission.NK.RankTheoryDeep.Refutation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corrected rank input: the **Hausdorff** quotient, not the torsion-free one

`Refutation.lean` shows that `NK.ShimizuRank.GammaTFRankFinite Ω ℓ` — equivalently, the
`rankFinite` field of `NK.ShimizuRank.Residuals Ω ℓ` — is **false**: the torsion-free quotient
`GammaTF K K' ℓ = Γ_K ⧸ torsion` of Shimizu's `Γ_K` has `ℤ_ℓ`-rank `ℵ₀` already for `K = ℚ`,
`ℓ = 2`.

The object whose `ℤ_ℓ`-rank really is Shimizu's invariant
`r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` is the **Hausdorff (dual-faithful) quotient**

  `NK.Reconstruct.HausQuot K K' ℓ = Γ_K ⧸ (invisible subgroup)`,

i.e. `Γ_K` modulo the subgroup of elements killed by every *continuous* character `Γ_K → ℤ_ℓ`
(`Submission/Work/Reconstruct/gammaSmul.lean`, `gammaHaus.lean`).  This is exactly the classical
object: `r_ℓ(K) = rank_{ℤ_ℓ} Hom_cts(Γ_K, ℤ_ℓ) = rank_{ℤ_ℓ} Hom_cts(C_K, ℤ_ℓ)`, the rank of the
character module of the idèle class group
(`NK.GlobalCFT.IdeleClassGroup`, CoNF Ch. X §10.3), which is *finite* and equal to
`r_ℂ(K) + 1 + δ_ℓ(K)` — the equation whose naive transcription to `Γ_K ⧸ torsion` is the error
refuted in `Refutation.lean`.  The two objects differ exactly by the invisible non-torsion elements
of `Γ_ℚ` (the `∏_n ℤ/2^n`-part exhibited in `ProductRank.lean`).

## What this file delivers

* `NK.RankTheoryDeep.HausQuotRankFinite Ω ℓ` — **the corrected replacement** of the falsified
  `GammaTFRankFinite`: the Hausdorff quotient of `Γ_K` has *finite* `ℤ_ℓ`-rank.  This is
  CoNF (10.3.20) in its correct form.  It is *strictly weaker* than the falsified statement and
  implies it under no circumstances; it is *implied by* the workspace's existing (and falsified for
  the same reason) `NK.Reconstruct.HausRankInput Ω ℓ` — see
  `NK.RankTheoryDeep.hausQuotRankFinite_of_hausRankInput`.
* `NK.RankTheoryDeep.rankGamma_rat_eq_zero` — unconditional (given the arithmetic surjection
  `Γ_ℚ ↠ ∏_n ℤ/2^n`): `rankGamma ℚ Ω 2 = 0`, purely by the `Cardinal.toNat` truncation.  This is
  the concrete mechanism by which *every* statement of the form `rankGamma ℚ Ω 2 = r` degenerates.
* `NK.RankTheoryDeep.not_hausRankInput_of_rank_hausQuot` — the inconsistency of the old
  `HausRankInput` with the idèle-side value `rank_{ℤ_ℓ} HausQuot ℚ Ω 2 = r_2(ℚ) = 1`: the old input
  forces `rank(HausQuot ℚ Ω 2) = ↑(rankGamma ℚ Ω 2) = 0`.
* `NK.RankTheoryDeep.CorrectedResiduals Ω ℓ` — the residual structure of
  `Submission/Work/ShimizuRank/Package.lean` with the falsified `rankFinite` field replaced by the
  correct `HausQuotRankFinite`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Cardinal

namespace NK.RankTheoryDeep

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The corrected rank input** (CoNF (10.3.20), in its correct form): the *Hausdorff* quotient
`Γ_K ⧸ invisible` — the quotient of the `ℓ`-adic abelianisation by the elements invisible to every
continuous character into `ℤ_ℓ`, i.e. the object whose continuous dual is `Hom_cts(Γ_K, ℤ_ℓ)` — has
**finite** `ℤ_ℓ`-rank.

This is the invariant `r_ℓ(K) = r_ℂ(K) + 1 + δ_ℓ(K)` of Shimizu's §4, and it is a theorem of
CoNF Ch. X §10.3: `Γ_K ⧸ invisible ≅ ℤ_ℓ^{r_ℓ(K)}`.  It must *not* be confused with
`NK.ShimizuRank.GammaTFRankFinite`, which asserts the same finiteness for the torsion-free
quotient and is false (`Refutation.lean`). -/
def HausQuotRankFinite (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'],
    Module.rank (PadicInt ℓ) (NK.Reconstruct.HausQuot K K' ℓ) < Cardinal.aleph0

/-- **`HausQuotRankFinite` follows from the workspace's `HausRankInput`**: `HausRankInput` identifies
the rank of `HausQuot K K' ℓ` with the natural number `rankGamma K K' ℓ`, in particular it is finite.
(We record this for the reduction; note that `HausRankInput` is itself falsified in
`NK.RankTheoryDeep.not_hausRankInput_of_rank_hausQuot` once the idèle-side rank of `ℚ` is known.) -/
theorem hausQuotRankFinite_of_hausRankInput {ℓ : ℕ} [Fact ℓ.Prime]
    (h : NK.Reconstruct.HausRankInput Ω ℓ) : HausQuotRankFinite Ω ℓ := by
  intro K _ _ K' _ _ _
  rw [h K K']
  exact_mod_cast Cardinal.natCast_lt_aleph0

/-- **`rankGamma ℚ Ω ℓ = 0`** — unconditionally given the arithmetic surjection `Γ_ℚ ↠ ∏_n ℤ/ℓ^n`:
the honest rank of `Γ_ℚ^{tf}` is infinite, and `rankGamma` is `Module.finrank`, i.e.
`Cardinal.toNat` of that rank, which is `0` on every infinite cardinal.  So *every* statement of the
form `rankGamma ℚ Ω ℓ = r` (and *every* statement comparing `rankGamma`-values at `ℚ`) degenerates
at `K = ℚ`. -/
theorem rankGamma_rat_eq_zero
    (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ) :
    NK.Reconstruct.rankGamma ℚ Ω 2 = 0 := by
  have h1 := aleph0_le_rank_gammaTF_rat Ω Φ hΦ
  have h2 : Module.finrank (PadicInt 2) (NK.Reconstruct.GammaTF (K := ℚ) (K' := Ω) 2) = 0 := by
    rw [Module.finrank]
    exact Cardinal.toNat_eq_zero.mpr (Or.inr h1)
  exact h2

/-- **The old `HausRankInput Ω 2` is inconsistent with the idèle-side value of `r_2(ℚ) = 1`.**

If the idèle-class-group computation of CoNF (10.3.20) — the corrected rank input — gives
`rank_{ℤ_2} (HausQuot ℚ Ω 2) = r_2(ℚ) = 1`, while the arithmetic surjection gives
`rankGamma ℚ Ω 2 = 0` (`NK.RankTheoryDeep.rankGamma_rat_eq_zero`), then
`NK.Reconstruct.HausRankInput Ω 2` — which asserts
`rank (HausQuot ℚ Ω 2) = ↑(rankGamma ℚ Ω 2)` — is **false**. -/
theorem not_hausRankInput_of_rank_hausQuot
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ)
    (hrank : Module.rank (PadicInt 2) (NK.Reconstruct.HausQuot (K := ℚ) (K' := Ω) 2) = 1) :
    ¬ NK.Reconstruct.HausRankInput Ω 2 := by
  intro h
  have h1 := h ℚ Ω
  rw [hrank, rankGamma_rat_eq_zero Ω Φ hΦ] at h1
  simp at h1

/-- **The corrected residual structure of the Shimizu rank chapter**: the four residuals of
`NK.ShimizuRank.Residuals` with the *falsified* `rankFinite : GammaTFRankFinite` replaced by the
correct `hausRankFinite : HausQuotRankFinite` (the finiteness of the rank of the *Hausdorff*
quotient, i.e. of `r_ℓ(K) = rank Hom_cts(Γ_K, ℤ_ℓ)`).

This is the structure that the Shimizu route should be wired against.  It does not imply the old
`Residuals` (by `Refutation.lean` the old structure is unsatisfiable), but every *consumer* of
`Residuals` in `Submission/Work/ShimizuRank/Package.lean` used the rank inputs only through
`rankGamma`-comparisons, which have to be replaced by comparisons of
`rank HausQuot`; see `README.md` for the precise list. -/
structure CorrectedResiduals (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω] (ℓ : ℕ) [Fact ℓ.Prime] : Prop where
  /-- CoNF (10.3.7) Cor. and the proof of (10.3.11) Cor. -/
  leopoldt : NK.ShimizuRank.LeopoldtDefectMono Ω ℓ
  /-- **the corrected form of (10.3.20)**: `Γ_K ⧸ invisible` has finite `ℤ_ℓ`-rank -/
  hausRankFinite : HausQuotRankFinite Ω ℓ
  /-- the rank computation of Proposition 4f.5 -/
  resKernel : NK.ShimizuRank.ResKernelRankInput Ω ℓ

/-- The corrected residual structure implies the *corrected* finiteness statement, and it is
consistent: there is no formal obstruction to supplying all four fields
(`NK.ShimizuRank.rankStrictMono_of_complex` uses only `leopoldt`, which is a theorem of
CoNF (10.3.7), and `hausRankFinite` is CoNF (10.3.20)). -/
theorem hausQuotRankFinite_of_corrected {ℓ : ℕ} [Fact ℓ.Prime]
    (h : CorrectedResiduals Ω ℓ) : HausQuotRankFinite Ω ℓ := h.hausRankFinite


/-! ## The Hausdorff quotient of `Γ_ℚ` is non-trivial, and `HausRankInput` is false -/

/-- **A non-zero continuous character of `Γ_ℚ` makes the Hausdorff quotient non-trivial**, hence of
positive rank: the character does not vanish on some `x ∈ Γ_ℚ`, so `x` is not invisible and its
image in `HausQuot ℚ Ω 2` is non-zero; that quotient is torsion-free
(`NK.ShimizuRank.hausQuot_torsionFree`), hence `Nontrivial`, hence of positive rank
(`Module.rank_pos`). -/
theorem rank_hausQuot_pos_of_dual_ne_zero
    {χ : NK.Reconstruct.Dual (NK.Reconstruct.Gamma ℚ Ω 2) 2} (hχ : χ ≠ 0) :
    0 < Module.rank (PadicInt 2) (NK.Reconstruct.HausQuot (K := ℚ) (K' := Ω) 2) := by
  classical
  have hx : ∃ x : Additive (NK.Reconstruct.Gamma ℚ Ω 2),
      (χ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →+ PadicInt 2) x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hχ (Subtype.ext (AddMonoidHom.ext h))
  obtain ⟨x, hx⟩ := hx
  have hxnot : x ∉ NK.Reconstruct.invisibleSubmodule (K := ℚ) (K' := Ω) (ℓ := 2) := by
    rw [NK.Reconstruct.mem_invisibleSubmodule_iff]
    exact fun h => hx (h χ)
  have hy : (Submodule.mkQ (NK.Reconstruct.invisibleSubmodule (K := ℚ) (K' := Ω) (ℓ := 2))) x
      ≠ 0 := by
    rw [Submodule.mkQ_apply]
    exact fun h => hxnot ((Submodule.Quotient.mk_eq_zero _).mp h)
  haveI : Nontrivial (NK.Reconstruct.HausQuot (K := ℚ) (K' := Ω) 2) :=
    ⟨⟨0, _, by simpa using hy.symm⟩⟩
  haveI : Module.IsTorsionFree (PadicInt 2)
      (NK.Reconstruct.HausQuot (K := ℚ) (K' := Ω) 2) :=
    NK.ShimizuRank.hausQuot_torsionFree
  exact rank_pos

/-- **`NK.Reconstruct.HausRankInput Ω 2` is false**, given the cyclotomic character
(`NK.RankTheoryDeep.exists_nontrivial_dual_rat`) and the refutation of the finiteness of the rank
of `Γ_ℚ^{tf}` (`NK.RankTheoryDeep.not_gammaTFRankFinite_of_surjection` by way of
`NK.RankTheoryDeep.rankGamma_rat_eq_zero`).

Indeed `HausRankInput` would force
`rank (HausQuot ℚ Ω 2) = ↑(rankGamma ℚ Ω 2) = ↑(toNat ℵ₀) = 0`, while the non-zero continuous
character gives `0 < rank (HausQuot ℚ Ω 2)`; this is the same computation that makes Shimizu's
`r_2(ℚ) = 1` fail for the *torsion-free* quotient `GammaTF`. -/
theorem not_hausRankInput_of_dual
    (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (hχ : ∃ χ : NK.Reconstruct.Dual (NK.Reconstruct.Gamma ℚ Ω 2) 2, χ ≠ 0)
    (Φ : Additive (NK.Reconstruct.Gamma ℚ Ω 2) →ₗ[PadicInt 2] EllTower 2)
    (hΦ : Function.Surjective Φ) :
    ¬ NK.Reconstruct.HausRankInput Ω 2 := by
  obtain ⟨χ, hχ⟩ := hχ
  have h1 := rank_hausQuot_pos_of_dual_ne_zero (Ω := Ω) hχ
  intro h
  have h2 := h ℚ Ω
  rw [rankGamma_rat_eq_zero Ω Φ hΦ] at h2
  rw [h2] at h1
  exact absurd h1 (lt_irrefl (0 : Cardinal))

end NK.RankTheoryDeep
