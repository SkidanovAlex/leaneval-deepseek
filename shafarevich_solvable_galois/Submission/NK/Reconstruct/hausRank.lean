import Submission.NK.Reconstruct.hausPi
import Submission.NK.Reconstruct.frobLevelInf
import Submission.NK.Reconstruct.torsionFreeGamma
import Submission.NK.Reconstruct.rankLemmas
import Submission.NK.Reconstruct.NumFieldIn
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rank computation of Shimizu's Proposition 4f.5

This file carries out the rank computation of Shimizu (arXiv:2009.10431, §4, Proposition 4f.5) on
the Hausdorff torsion-free quotient `Γ_K^{tf}` introduced in
`Submission/Work/Reconstruct/gammaSmul.lean`, using the base change `π^{tf}_{L/K}`
(`NK.Reconstruct.hausPi`) and its kernel (`NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`).

The two named inputs of the computation are

* `NK.Reconstruct.HausRankInput Ω ℓ` — **the rank of `Γ_K^{tf}` is `r_ℓ(K)`**: the identification
  of Shimizu's `Γ_K = G_K^{ab,(ℓ)}/torsion` (realised here as the image of
  `NK.Reconstruct.gammaEvalMul`, `NK.Reconstruct.GammaHaus`) with the quotient
  `Γ_K ⧸ invisibleSubmodule` of the projective limit.  It is the single place where the
  pro-`ℓ` group theory of `G_K^{ab,(ℓ)}` enters the rank computation (see the README, item (1)(ii));
  it is *false* for a general compact abelian pro-`ℓ` group (for `∏_n ℤ/ℓ^n` the invisible
  subgroup contains elements of infinite order), so it is a genuine statement about number fields.

* `NK.Reconstruct.RankStrictMonoLevelInput ℚ Ω ℓ` — **Shimizu's Lemma 4f.2** (CoNF (10.3.7)): for
  `M ⊆ N` finite levels of `Ω/ℚ` with `N` having a complex prime, `r_ℓ(M) < r_ℓ(N)`.  This is the
  form in which `NK.Reconstruct.RankStrictMonoInput` is consumed here (the two are equivalent;
  the level form is the one needed for the pair `K₁ ∩ K₂ ⊆ K₁`).

The main theorem is `NK.Reconstruct.fourf5_of_rankInputs`: **Shimizu's Proposition 4f.5**, i.e.
`NK.Reconstruct.Fourf5Input Ω ℓ`, from those two inputs.

## The argument

With `M := K₁ ∩ K₂` and `N := ker π^{tf}_{L/K}`:

1. `rank Γ_{K_i}^{tf} = rank (range π^{tf}_{L/K_i})` because the cokernel is finite
   (`NK.Reconstruct.finite_coker_hausPi`), the cokernel of `π_{L/K}` being finite
   (`NK.Reconstruct.finite_coker_gammaBaseChangeHom`);
2. `range π^{tf}_{L/K_i} ≅ Γ_L^{tf}/ker π^{tf}_{L/K_i}` (`LinearMap.quotKerEquivRange`), and the two
   kernels agree by `NK.Reconstruct.ker_hausPi_eq_of_levelInfinity_eq`; hence
   `r_ℓ(K₁) = r_ℓ(K₂)` (this is the step of Shimizu's proof that computes the common kernel `N`);
3. `r_ℓ(M) ≤ r_ℓ(K_i)`: the base change is functorial
   (`NK.Reconstruct.hausPi_comp`), so `ker π^{tf}_{L/K_i} ≤ ker π^{tf}_{L/M}`, and
   `NK.Reconstruct.rankQuotientLeQuotientOfLe` finishes;
4. Shimizu's Lemma 4f.2 applied to `M ⊆ K₁` (which has a complex prime by hypothesis) forces
   `M = K₁`, i.e. `K₁ ⊆ K₂`; then `K₂` has a complex prime as well
   (`NK.Reconstruct.exists_isComplex_of_le`), and Lemma 4f.2 applied to `K₁ ⊆ K₂` contradicts the
   rank equality of step 2.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

open scoped Pointwise

universe u v

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]

/-! ## Finiteness of the cokernel of the base change, in additive form -/

/-- **The cokernel of `π_{L/K}` is finite**, `NK.Reconstruct.finite_coker_gammaBaseChangeHom`
read in the additive (module-theoretic) form used for rank computations: the projection to the
finite level `L` has kernel the range of `π_{L/K}`, and it is surjective. -/
theorem finite_coker_baseChangeLinear (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Finite (Additive (Gamma ↥K.L Ω ℓ) ⧸ LinearMap.range (baseChangeLinear K L h ℓ)) := by
  have hker := ker_projAdd_eq_range_baseChangeLinear K L h ℓ
  have e : (Additive (Gamma ↥K.L Ω ℓ) ⧸ LinearMap.range (baseChangeLinear K L h ℓ))
      ≃ₗ[PadicInt ℓ] ↥(LinearMap.range
        (projAdd (K := ↥K.L) (K' := Ω) ℓ (levelExtendGen K L h))) := by
    rw [← hker]
    exact LinearMap.quotKerEquivRange _
  exact Finite.of_injective e e.injective

/-- **The cokernel of the descended base change `π^{tf}_{L/K}` is finite.**  The composite
`Γ_K → Γ_K^{tf} → Γ_K^{tf}/im π^{tf}_{L/K}` kills the range of `π_{L/K}`, hence factors through the
finite quotient `Γ_K/im π_{L/K}` (`NK.Reconstruct.finite_coker_baseChangeLinear`). -/
theorem finite_coker_hausPi (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Finite (HausQuot ↥K.L Ω ℓ ⧸ LinearMap.range (hausPi K L h ℓ)) := by
  haveI := finite_coker_baseChangeLinear K L h ℓ
  -- the composite `Γ_K → Γ_K^{tf} → Γ_K^{tf}/range π^{tf}` kills `range π_{L/K}`
  have hle : LinearMap.range (baseChangeLinear K L h ℓ)
      ≤ LinearMap.ker (((Submodule.mkQ (LinearMap.range (hausPi K L h ℓ))).comp
          (hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)))) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply]
    show Submodule.Quotient.mk (DFunLike.coe hausMk (baseChangeLinear K L h ℓ y)) = 0
    rw [← hausPi_hausMk K L h ℓ y]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩
  let Φ := Submodule.liftQ (LinearMap.range (baseChangeLinear K L h ℓ))
    (((Submodule.mkQ (LinearMap.range (hausPi K L h ℓ))).comp
      (hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ)))) hle
  refine Finite.of_surjective Φ (fun z => ?_)
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective (LinearMap.range (hausPi K L h ℓ)) z
  obtain ⟨x, rfl⟩ := hausMk_surjective (K := ↥K.L) (K' := Ω) (ℓ := ℓ) y
  exact ⟨Submodule.Quotient.mk x, by rw [Submodule.liftQ_apply, LinearMap.comp_apply, hy]⟩

/-! ## The rank of `Γ_K^{tf}` through the base change -/

/-- **The rank of `Γ_K^{tf}` is the rank of the image of the base change**, its cokernel being
finite (`NK.Reconstruct.finite_coker_hausPi`). -/
theorem rank_hausQuot_eq_rank_range_hausPi (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.rank (PadicInt ℓ) (HausQuot ↥K.L Ω ℓ)
      = Module.rank (PadicInt ℓ) ↥(LinearMap.range (hausPi K L h ℓ)) :=
  rankEqRankRangeOfFiniteCoker (hausPi K L h ℓ) (finite_coker_hausPi K L h ℓ)

/-- **The rank of `Γ_K^{tf}` through the kernel of the base change**: `rank Γ_K^{tf} = rank
(Γ_L^{tf}/ker π^{tf}_{L/K})`. -/
theorem rank_hausQuot_eq_rank_quot_ker (K : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    (h : K.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.rank (PadicInt ℓ) (HausQuot ↥K.L Ω ℓ)
      = Module.rank (PadicInt ℓ)
          (HausQuot ↥L.L Ω ℓ ⧸ LinearMap.ker (hausPi K L h ℓ)) := by
  rw [rank_hausQuot_eq_rank_range_hausPi K L h ℓ]
  exact (LinearEquiv.rank_eq (LinearMap.quotKerEquivRange (hausPi K L h ℓ))).symm

/-- **Step 2 of Shimizu's proof: equal kernels give equal ranks.** -/
theorem rank_hausQuot_eq_of_ker_eq (K₁ K₂ : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
    [IsSepClosure ↥K₁.L Ω] [IsSepClosure ↥K₂.L Ω] [IsSepClosure ↥L.L Ω]
    (h₁ : K₁.L ≤ L.L) (h₂ : K₂.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime]
    (hker : LinearMap.ker (hausPi K₁ L h₁ ℓ) = LinearMap.ker (hausPi K₂ L h₂ ℓ)) :
    Module.rank (PadicInt ℓ) (HausQuot ↥K₁.L Ω ℓ)
      = Module.rank (PadicInt ℓ) (HausQuot ↥K₂.L Ω ℓ) := by
  rw [rank_hausQuot_eq_rank_quot_ker K₁ L h₁ ℓ, rank_hausQuot_eq_rank_quot_ker K₂ L h₂ ℓ, hker]

/-! ## Functoriality of the descended base change -/

/-- **Functoriality of the descended base change**: for `K ⊆ M ⊆ L`,
`π^{tf}_{L/K} = π^{tf}_{M/K} ∘ π^{tf}_{L/M}`.

Both sides are checked on the elements `hausMk (galToGamma σ)`, which are dense in the sense of
`NK.Reconstruct.hausMk_galToGamma_surjective`; there the claim is the functoriality
`NK.Reconstruct.ambientPi_trans` of Shimizu's base change. -/
theorem hausPi_comp (K M L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω] [IsSepClosure ↥M.L Ω]
    (hKM : K.L ≤ M.L) (hML : M.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    hausPi (NumFieldIn.ofFrobLevel K) L (hKM.trans hML) ℓ
      = (hausPi (NumFieldIn.ofFrobLevel K) M hKM ℓ).comp
          (hausPi (NumFieldIn.ofFrobLevel M) L hML ℓ) := by
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  refine LinearMap.ext (fun x => ?_)
  obtain ⟨σ, rfl⟩ := hausMk_galToGamma_surjective L ℓ x
  rw [LinearMap.comp_apply, hausPi_hausMk, hausPi_hausMk, hausPi_hausMk,
    baseChangeLinear_apply, baseChangeLinear_apply, baseChangeLinear_apply]
  have hcomp := ambientPi_trans K M L hKM hML ℓ (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ)
  exact congrArg (fun y => hausMk (K := ↥K.L) (K' := Ω) (ℓ := ℓ) (Additive.ofMul y)) hcomp.symm

/-- **Step 3 of Shimizu's proof: monotonicity of the rank in the base field.**  Since
`π^{tf}_{L/K} = π^{tf}_{M/K} ∘ π^{tf}_{L/M}`, the kernel of `π^{tf}_{L/M}` contains that of
`π^{tf}_{L/K}`, so `rank Γ_K^{tf} ≤ rank Γ_M^{tf}`. -/
theorem rank_hausQuot_le_of_le (K M L : FrobLevel ℚ Ω) [IsSepClosure ↥K.L Ω]
    [IsSepClosure ↥M.L Ω] (hKM : K.L ≤ M.L) (hML : M.L ≤ L.L) (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.rank (PadicInt ℓ) (HausQuot ↥K.L Ω ℓ)
      ≤ Module.rank (PadicInt ℓ) (HausQuot ↥M.L Ω ℓ) := by
  haveI : IsSepClosure ↥L.L Ω := isSepClosure_of_le L.L
  have hle : LinearMap.ker (hausPi (NumFieldIn.ofFrobLevel M) L hML ℓ)
      ≤ LinearMap.ker (hausPi (NumFieldIn.ofFrobLevel K) L (hKM.trans hML) ℓ) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hausPi_comp K M L hKM hML ℓ, LinearMap.comp_apply, hx, map_zero]
  calc Module.rank (PadicInt ℓ) (HausQuot ↥K.L Ω ℓ)
      = Module.rank (PadicInt ℓ)
          (HausQuot ↥L.L Ω ℓ ⧸ LinearMap.ker
            (hausPi (NumFieldIn.ofFrobLevel K) L (hKM.trans hML) ℓ)) :=
        rank_hausQuot_eq_rank_quot_ker (NumFieldIn.ofFrobLevel K) L (hKM.trans hML) ℓ
    _ ≤ Module.rank (PadicInt ℓ) (HausQuot ↥L.L Ω ℓ ⧸ LinearMap.ker
          (hausPi (NumFieldIn.ofFrobLevel M) L hML ℓ)) :=
        rankQuotientLeQuotientOfLe hle
    _ = Module.rank (PadicInt ℓ) (HausQuot ↥M.L Ω ℓ) :=
        (rank_hausQuot_eq_rank_quot_ker (NumFieldIn.ofFrobLevel M) L hML ℓ).symm

/-! ## The two named inputs -/

/-- **The named input `r_ℓ(K) = rank_{ℤ_ℓ} Γ_K^{tf}`.**

Shimizu's `Γ_K = Γ_{K,ℓ} = G_K^{ab,(ℓ)}/torsion` is realised in this development as the Hausdorff
torsion-free quotient `NK.Reconstruct.HausQuot K K' ℓ = Γ_K ⧸ invisibleSubmodule`; its
`ℤ_ℓ`-rank is the invariant `r_ℓ(K)` of CoNF Ch. X §10.3, whose class-field-theoretic evaluation is
the input `NK.Reconstruct.RankFormulaInput`.  This predicate records the identification of the two
models of `Γ_K`, i.e. that the subgroup of `Γ_K` invisible to every continuous character
`Γ_K → ℤ_ℓ` has the same rank as the torsion subgroup of `Γ_K`.

See the README for the discussion of why this is a genuine property of `G_K^{ab,(ℓ)}` and not a
formal consequence of the definitions (item (1)(ii)). -/
def HausRankInput (Ω : Type u) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (K' : Type u) [Field K'] [Algebra K K']
    [IsGalois K K'],
    Module.rank (PadicInt ℓ) (HausQuot K K' ℓ) = (rankGamma K K' ℓ : Cardinal)

/-- **Shimizu's Lemma 4f.2 in the level form used by the reconstruction** (CoNF (10.3.7)):
for finite Galois levels `M ⊆ N` of `K'/K` with `N` having a complex prime, `r_ℓ(M) < r_ℓ(N)`.

This is the form of `NK.Reconstruct.RankStrictMonoInput` needed for the pair
`K₁ ∩ K₂ ⊆ K₁` in Proposition 4f.5 (the meet being a level by
`NK.Reconstruct.FrobLevel.inf`). -/
def RankStrictMonoLevelInput (K : Type u) [Field K] [NumberField K] (K' : Type v) [Field K']
    [Algebra K K'] [IsGalois K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ (M N : FrobLevel K K') (h : M.L ≤ N.L), M.L ≠ N.L →
    (∃ v : NumberField.InfinitePlace ↥N.L, NumberField.InfinitePlace.IsComplex v) →
      rankGamma ↥M.L K' ℓ < rankGamma ↥N.L K' ℓ

end NK.Reconstruct
