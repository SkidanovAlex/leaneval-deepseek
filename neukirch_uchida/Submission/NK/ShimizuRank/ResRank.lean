import Submission.NK.ShimizuRank.Basic
import Submission.NK.ShimizuRank.HausRank

/-!
# `NK.Reconstruct.ResRankInputGen` from `ResKernelRankInput`

`NK.Reconstruct.ResRankInputGen Ω ℓ` is the rank computation inside Shimizu's Proposition 4f.5:
with `M = K₁ ∩ K₂` and a finite level `L ⊇ K₁, K₂` such that `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}`, one has
`r_ℓ(K₁) ≤ r_ℓ(M)`.

## The two halves

**The proved half.**  For `K ⊆ L` finite levels, the cokernel of the base change
`π^{tf}_{L/K} : Γ_L^{tf} → Γ_K^{tf}` is finite (`NK.Reconstruct.finite_coker_hausPi`), so
`r_ℓ(K) = rank_{ℤ_ℓ}(Γ_L^{tf} ⧸ ker π^{tf}_{L/K})`
(`NK.Reconstruct.rank_hausQuot_eq_rank_quot_ker`).  Since `M = K₁ ∩ K₂ ⊆ K₁`, the functoriality
`π^{tf}_{L/M} = π^{tf}_{K₁/M} ∘ π^{tf}_{L/K₁}` gives `ker π^{tf}_{L/K₁} ≤ ker π^{tf}_{L/M}`, and
passing to the quotient gives `r_ℓ(M) ≤ r_ℓ(K₁)`
(`NK.Reconstruct.rank_hausQuot_le_of_le`).  So the *general* direction is
`r_ℓ(M) ≤ r_ℓ(K₁)`, and `ResRankInputGen` asserts the reverse inequality in the special
situation of Prop. 4f.5.

**The input.**  `NK.ShimizuRank.ResKernelRankInput Ω ℓ` states the reverse inequality in the
kernel form: `rank (Γ_L^{tf} ⧸ ker π^{tf}_{L/M}) ≥ rank (Γ_L^{tf} ⧸ ker π^{tf}_{L/K₁})`.  The
hypothesis `K₁^{(∞,ℓ)}L = LK₂^{(∞,ℓ)}` is exactly what makes
`ker π^{tf}_{L/K₁} = ker π^{tf}_{L/K₂}`
(`NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`); the extra content is then Shimizu's
finite-index argument: the two images `im(res^{K₁})`, `im(res^{K₂})` of the dual maps inside
`Hom(Γ_L, ℤ_ℓ)` have rank `r_ℓ(K₁)` (Lemma 4f.1) and both are contained in
`Hom(Γ_L/N, ℤ_ℓ)`, `N = ker π^{tf}_{L/K₁}`, of the same rank, whence their intersection also has
rank `r_ℓ(K₁)`; and that intersection consists of the forms killing `ker π^{tf}_{L/M}`, so it lies
in `im(res^{M})`, whose rank is `r_ℓ(M)`.

## Main results

* `NK.ShimizuRank.resRankInputGen_of_residual` — `ResRankInputGen` from `HausRankInput` and
  `ResKernelRankInput`;
* `NK.ShimizuRank.resKernelRankInput_of_resRankInput` — the converse (modulo `HausRankInput`), so
  the reduction is lossless;
* `NK.ShimizuRank.resRankInputGen_iff_resKernelRankInput`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.ShimizuRank

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **`ResRankInputGen` from the two residuals.**  Taking the identification of the two models of
`Γ_K` (`HausRankInput`) and the kernel-rank computation (`ResKernelRankInput`), Shimizu's rank
computation of Proposition 4f.5 follows: both `r_ℓ(K₁)` and `r_ℓ(M)` are the ranks of the
corresponding quotients of `Γ_L^{tf}` by the kernels of the base change
(`NK.Reconstruct.rank_hausQuot_eq_rank_quot_ker`), and `ResKernelRankInput` compares those two
quotient ranks. -/
theorem resRankInputGen_of_residual {ℓ : ℕ} [Fact ℓ.Prime]
    (hH : HausRankInput Ω ℓ) (hK : ResKernelRankInput Ω ℓ) : ResRankInputGen Ω ℓ := by
  intro K₁ K₂ M L _ _ _ hMsup h₁ h₂ hsup
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  have hM : M.L ≤ L.L := by rw [hMsup]; exact le_trans inf_le_left h₁
  have hr₁ := rank_hausQuot_eq_rank_quot_ker K₁ L h₁ ℓ
  have hrM := rank_hausQuot_eq_rank_quot_ker M L hM ℓ
  have hcard : (rankGamma ↥K₁.L Ω ℓ : Cardinal) ≤ (rankGamma ↥M.L Ω ℓ : Cardinal) := by
    rw [← hH ↥K₁.L Ω, ← hH ↥M.L Ω, hr₁, hrM]
    exact hK K₁ K₂ M L hMsup h₁ h₂ hM hsup
  exact_mod_cast hcard

/-- **The converse**: given `HausRankInput`, `ResRankInputGen` is equivalent to the kernel-rank
computation `ResKernelRankInput`.  Hence replacing `ResRankInputGen` by `ResKernelRankInput` loses
nothing. -/
theorem resKernelRankInput_of_resRankInput {ℓ : ℕ} [Fact ℓ.Prime]
    (hH : HausRankInput Ω ℓ) (hR : ResRankInputGen Ω ℓ) : ResKernelRankInput Ω ℓ := by
  intro K₁ K₂ M L _ _ _ _ hMsup h₁ h₂ hM hsup
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  have hr₁ := rank_hausQuot_eq_rank_quot_ker K₁ L h₁ ℓ
  have hrM := rank_hausQuot_eq_rank_quot_ker M L hM ℓ
  have hcard : (rankGamma ↥K₁.L Ω ℓ : Cardinal) ≤ (rankGamma ↥M.L Ω ℓ : Cardinal) := by
    exact_mod_cast hR K₁ K₂ M L hMsup h₁ h₂ hsup
  rw [← hH ↥K₁.L Ω, ← hH ↥M.L Ω, hr₁, hrM] at hcard
  exact hcard

/-- **The lossless decomposition of `ResRankInputGen`**, modulo the identification of the models of
`Γ_K`. -/
theorem resRankInputGen_iff_resKernelRankInput {ℓ : ℕ} [Fact ℓ.Prime]
    (hH : HausRankInput Ω ℓ) : ResRankInputGen Ω ℓ ↔ ResKernelRankInput Ω ℓ :=
  ⟨resKernelRankInput_of_resRankInput hH, resRankInputGen_of_residual hH⟩

end NK.ShimizuRank

namespace NK.ShimizuRank

open NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

universe u

variable {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-- **The *proved* half of the rank computation of Shimizu's Proposition 4f.5**: for finite levels
`K ⊆ M ⊆ L` of `Ω/ℚ`, the ℓ-rank is monotone, `r_ℓ(K) ≤ r_ℓ(M)`.

This is unconditional modulo the identification of the two models of `Γ_K`
(`NK.Reconstruct.HausRankInput`): the base change `π^{tf}_{L/K}` factors as
`π^{tf}_{M/K} ∘ π^{tf}_{L/M}`, so `ker π^{tf}_{L/K} ≤ ker π^{tf}_{L/M}`, and passing to the quotient
gives the inequality (`NK.Reconstruct.rank_hausQuot_le_of_le`).  The residual
`NK.ShimizuRank.ResKernelRankInput` is precisely the *reverse* inequality in the situation of
Prop. 4f.5. -/
theorem rankGamma_le_of_le {ℓ : ℕ} [Fact ℓ.Prime] (hH : HausRankInput Ω ℓ)
    (K M L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω] [IsSepClosure ↥M.L Ω]
    (hKM : K.L ≤ M.L) (hML : M.L ≤ L.L) :
    rankGamma ↥K.L Ω ℓ ≤ rankGamma ↥M.L Ω ℓ := by
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  have h := rank_hausQuot_le_of_le K M L hKM hML ℓ
  rw [hH ↥K.L Ω, hH ↥M.L Ω] at h
  exact_mod_cast h

/-- **The `FrobLevel` form of `ResRankInputGen`** (the version `NK.Reconstruct.ResRankInput`
consumed by `Submission/Work/Reconstruct/fourf5Rank.lean`): a statement for all number-field levels
implies the same statement for the Galois-over-`ℚ` levels. -/
theorem resRankInput_of_gen {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    {ℓ : ℕ} [Fact ℓ.Prime] (h : ResRankInputGen Ω ℓ) : ResRankInput Ω ℓ := by
  intro K₁ K₂ M L _ _ _ hML h₁ h₂ hsup
  exact h (NumFieldIn.ofFrobLevel K₁) (NumFieldIn.ofFrobLevel K₂) (NumFieldIn.ofFrobLevel M) L
    hML h₁ h₂ hsup

/-- **The `FrobLevel` form of the *proved* monotonicity**: for finite levels `K ⊆ M ⊆ L`, the ℓ-rank is
monotone.  This is the re-export of `NK.Reconstruct.rank_hausQuot_le_of_le` in terms of
`rankGamma`, under the identification `HausRankInput`. -/
theorem rankGamma_le_of_le_level {ℓ : ℕ} [Fact ℓ.Prime] (hH : HausRankInput Ω ℓ)
    (K M L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω] [IsSepClosure ↥M.L Ω]
    (hKM : K.L ≤ M.L) (hML : M.L ≤ L.L) :
    rankGamma ↥K.L Ω ℓ ≤ rankGamma ↥M.L Ω ℓ :=
  rankGamma_le_of_le hH K M L hKM hML

end NK.ShimizuRank
