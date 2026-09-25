import Mathlib
import Submission.NK.NUV2.Wall
import Submission.NK.RankTheoryDeep.All
import Submission.NK.NUV2.localUnits_two
import Submission.NK.NUV2.ideleDefs
import Submission.NK.NUV2.ideleDefectData
import Submission.NK.NUV2.rank_dual_integralIdeles_eq_finrank
import Submission.NK.NUV2.rank_unitsDual_le
import Submission.NK.NUV2.ideleDualRank_finrank_lowerBound
import Submission.NK.NUV2.localUnitDualRank_lowerBound
import Submission.NK.NUV2.unitsImgRank_naturality

/-!
# `ideleDefectMono_attempt` — the monotonicity of the idèle-side defect

CoNF (10.3.7) Corollary + (10.3.20) on the idèle class group: for number fields `M ⊆ N`,

`finrank (Hom_cts(C_M, ℤ_2)) - r_ℂ(M) ≤ finrank (Hom_cts(C_N, ℤ_2)) - r_ℂ(N)`.

The vocabulary (`NK.NUV2.idcDualRank` `a_K`, `NK.NUV2.intDualRank` `m_K`,
`NK.NUV2.unitsImgRank` `u_K`, `NK.NUV2.defectRho` `ρ_K`) is in
`Submission/Work/NUV2/ideleDefectData.lean`.  The proof is the reduction

* `m_K = [K : ℚ]`  (`NUV2/rank_dual_integralIdeles_eq_finrank`: the sharp local unit structure
  `rank Hom_cts(𝒪_vˣ, ℤ_2) = e_v f_v` at the places `v | 2`),
* `a_K + u_K = m_K` (the exactness of the dual sequence `Dual C_K → Dual 𝕀_int K → Dual 𝒪_Kˣ`, the
  class group being finite so the cokernel is torsion),
* `u_N ≤ u_M + (ρ_N - ρ_M)` for `M ⊆ N` (base change of the relations among the units),

together with the monotonicity of the infinite-place count `ρ`.  Indeed then
`a_K = m_K - u_K = ρ_K + r_ℂ(K) + 1 - u_K` and the inequality is `u_N - u_M ≤ ρ_N - ρ_M`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT
open scoped NumberField

namespace NK.NUV2

/-- **`ρ` is monotone**: an infinite place of `M` has at least one place of `N` above it, so the
number of infinite places does not decrease (and `defectRho K = #InfinitePlace K - 1` because a
number field has at least one infinite place). -/
theorem defectRho_mono (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N] (hMN : M ≤ N) :
    defectRho ↥M ≤ defectRho ↥N := by
  haveI : Algebra ↥M ↥N := (IntermediateField.inclusion hMN).toAlgebra
  haveI : IsScalarTower ℚ ↥M ↥N := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    ext
    simp [IntermediateField.inclusion, RingHom.algebraMap_toAlgebra]
  have hcard : Nat.card (NumberField.InfinitePlace ↥M)
      ≤ Nat.card (NumberField.InfinitePlace ↥N) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact NumberField.InfinitePlace.card_mono ↥M ↥N
  have h1 : defectRho ↥M = Nat.card (NumberField.InfinitePlace ↥M) - 1 := by
    rw [defectRho, ← NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      Nat.card_eq_fintype_card]
  have h2 : defectRho ↥N = Nat.card (NumberField.InfinitePlace ↥N) - 1 := by
    rw [defectRho, ← NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      Nat.card_eq_fintype_card]
  rw [h1, h2]
  exact Nat.sub_le_sub_right hcard 1

/-! ## The two directions of the exactness at `Dual 𝕀_int K` -/

/-- **A continuous character of `C_K` restricted to the integral idèles kills the global units.**
The image of `u ∈ 𝒪_Kˣ` in `C_K` is the class of the principal idèle `(u)`, which is trivial. -/
theorem restrictUnits_dualMap_integralIdeles_apply (K : Type) [Field K] [NumberField K]
    (χ : NK.Reconstruct.Dual (IdeleClassGroup K) 2) (u : (NumberField.RingOfIntegers K)ˣ) :
    restrictUnits (K := K)
        (NK.Reconstruct.dualMap 2 (NK.RankTheoryDeep.integralIdelesToClassGroup K)
          (NK.RankTheoryDeep.continuous_integralIdelesToClassGroup K) χ)
        (Additive.ofMul u) = 0 := by
  rw [restrictUnits_apply, NK.Reconstruct.dualMap_apply]
  have h1 : (NK.RankTheoryDeep.integralIdelesToClassGroup K) (unitsToIntegral K u) = 1 := by
    rw [NK.RankTheoryDeep.integralIdelesToClassGroup, MonoidHom.comp_apply,
      IdeleClassGroup.mk_apply]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    change ((unitsToIntegral K u : ↥(Idele.integralIdeles K)) : Idele K) ∈
      Idele.principalSubgroup K
    rw [unitsToIntegral_coe]
    exact Idele.mem_principalSubgroup.mpr ⟨_, rfl⟩
  show χ (Additive.ofMul ((NK.RankTheoryDeep.integralIdelesToClassGroup K)
      (unitsToIntegral K u))) = 0
  rw [h1, ofMul_one, map_zero]

/-- **The exactness direction `a_K ≤ rank (ker (restrictUnits K))`**: restricting a continuous
character of `C_K` to the integral idèles produces a character killing `𝒪_Kˣ`, and the map is
injective because a character vanishing on `𝕀_int K` is zero (the class group is finite,
`dualMap_integralIdelesToClassGroup_eq_zero`). -/
theorem rank_idcDualRank_le_rank_ker (K : Type) [Field K] [NumberField K] :
    Module.rank (PadicInt 2) (NK.Reconstruct.Dual (IdeleClassGroup K) 2)
      ≤ Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker := by
  have hcont := NK.RankTheoryDeep.continuous_integralIdelesToClassGroup K
  let Φ : NK.Reconstruct.Dual (IdeleClassGroup K) 2 →ₗ[PadicInt 2]
      NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) 2 :=
    { toFun := NK.Reconstruct.dualMap 2 (NK.RankTheoryDeep.integralIdelesToClassGroup K) hcont
      map_add' := fun f g =>
        NK.Reconstruct.dualMap_add 2 (NK.RankTheoryDeep.integralIdelesToClassGroup K) hcont f g
      map_smul' := by
        intro a f
        apply Subtype.ext
        apply AddMonoidHom.ext
        intro x
        simp [NK.Reconstruct.dualMap_apply, NK.RankTheoryDeep.smul_dual_apply] }
  have hinj : Function.Injective Φ := by
    intro f g hfg
    have hzero : Φ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
    exact sub_eq_zero.mp
      (NK.RankTheoryDeep.dualMap_integralIdelesToClassGroup_eq_zero K (f - g) hzero)
  have hrange : Φ.range ≤ (restrictUnits (K := K)).ker := by
    rintro x ⟨χ, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    apply AddMonoidHom.ext
    intro y
    conv_lhs => rw [← ofMul_toMul y]
    exact restrictUnits_dualMap_integralIdeles_apply K χ (Additive.toMul y)
  calc Module.rank (PadicInt 2) (NK.Reconstruct.Dual (IdeleClassGroup K) 2)
      = Module.rank (PadicInt 2) ↥Φ.range :=
        (LinearEquiv.ofInjective Φ hinj).rank_eq
    _ ≤ Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker := Submodule.rank_mono hrange

/-- **The exactness `a_K + u_K = m_K`** from the two directions of the exactness at `Dual 𝕀_int K`:
the rank–nullity of `restrictUnits K` together with `a_K = rank (ker (restrictUnits K))`. -/
theorem idcDualRank_add_unitsImgRank_of_le (K : Type) [Field K] [NumberField K]
    (hker : Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker
      ≤ Module.rank (PadicInt 2) (NK.Reconstruct.Dual (IdeleClassGroup K) 2)) :
    idcDualRank K + unitsImgRank K = intDualRank K := by
  have hrn := LinearMap.rank_range_add_rank_ker (restrictUnits (K := K))
  have h2 : Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker
      = Module.rank (PadicInt 2) (NK.Reconstruct.Dual (IdeleClassGroup K) 2) :=
    le_antisymm hker (rank_idcDualRank_le_rank_ker K)
  have hfin : Module.rank (PadicInt 2) (NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) 2)
      < Cardinal.aleph0 :=
    lt_of_le_of_lt (NK.RankTheoryDeep.rank_dual_integralIdeles_le K NK.NUV2.localUnits_two)
      (by exact_mod_cast Cardinal.natCast_lt_aleph0)
  have hfinU : Module.rank (PadicInt 2) (Additive ((NumberField.RingOfIntegers K)ˣ) →+ PadicInt 2)
      < Cardinal.aleph0 :=
    lt_of_le_of_lt (NK.NUV2.rank_unitsDual_le K) (by exact_mod_cast Cardinal.natCast_lt_aleph0)
  have hfink : Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker < Cardinal.aleph0 :=
    lt_of_le_of_lt (Submodule.rank_mono (le_top :
      (restrictUnits (K := K)).ker ≤ ⊤)) (by
        rw [Submodule.topEquiv.rank_eq]; exact hfin)
  have hfinr : Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).range < Cardinal.aleph0 :=
    lt_of_le_of_lt (Submodule.rank_mono (le_top :
      (restrictUnits (K := K)).range ≤ ⊤)) (by
        rw [Submodule.topEquiv.rank_eq]; exact hfinU)
  simp only [idcDualRank, intDualRank, unitsImgRank, Module.finrank]
  rw [← h2, ← hrn]
  rw [add_comm (Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).range)
    (Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker)]
  rw [Cardinal.toNat_add hfink hfinr]

/-- **From the cardinal equality `rank (Dual 𝕀_int K) = [K : ℚ]` to the `finrank` form.** -/
theorem intDualRank_eq_finrank_of_rank_eq (K : Type) [Field K] [NumberField K]
    (h : Module.rank (PadicInt 2) (NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) 2)
      = (Module.finrank ℚ K : Cardinal)) :
    intDualRank K = Module.finrank ℚ K := by
  have h' : (Module.rank (PadicInt 2)
        (NK.Reconstruct.Dual (↥(Idele.integralIdeles K)) 2)).toNat
      = Module.finrank ℚ K := by
    rw [h, Cardinal.toNat_natCast]
  exact h'

/-- **The reduction.**  The three components (sharp local structure, exactness, base change of the
relations) imply the monotonicity of the idèle-side defect. -/
theorem ideleDefectMono_of_components (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω]
    (hint : ∀ (K : Type) [Field K] [NumberField K], intDualRank K = Module.finrank ℚ K)
    (hex : ∀ (K : Type) [Field K] [NumberField K],
      idcDualRank K + unitsImgRank K = intDualRank K)
    (hnat : ∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N →
      unitsImgRank ↥N ≤ unitsImgRank ↥M + (defectRho ↥N - defectRho ↥M)) :
    ∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N →
      Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (IdeleClassGroup ↥M) 2)
          - NK.Reconstruct.rComplex ↥M
        ≤ Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (IdeleClassGroup ↥N) 2)
          - NK.Reconstruct.rComplex ↥N := by
  intro M N _ _ hMN
  have hM := hint ↥M
  have hN := hint ↥N
  have heM := hex ↥M
  have heN := hex ↥N
  have hn := hnat M N hMN
  have hr := defectRho_mono Ω M N hMN
  have h1 := defectRho_add_rComplex_add_one ↥M
  have h2 := defectRho_add_rComplex_add_one ↥N
  simp only [idcDualRank, intDualRank] at hM hN heM heN
  omega


/-- **The requested lemma from the two classical inputs and the base change of the relations.**

The inputs are:

* `hloc`: the sharp local unit structure `rank Hom_cts(𝒪_qˣ, ℤ_2) = e_q f_q` at the places `q | 2`
  (`NUV2/localUnitDualRank_lowerBound`), which via `NUV2/rank_dual_integralIdeles_eq_finrank` gives
  `m_K = [K : ℚ]`;
* `hker`: `rank (ker (restrictUnits K)) ≤ rank (Hom_cts(C_K, ℤ_2))` — the extension of characters
  of `𝕀_int K` killing `𝒪_Kˣ` to `C_K`, which with `rank_idcDualRank_le_rank_ker` gives the
  exactness `a_K + u_K = m_K`;
* the base change of the relations (`NUV2/unitsImgRank_naturality`) `u_N ≤ u_M + (ρ_N - ρ_M)`. -/
theorem ideleDefectMono_attempt_of_components (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
    [IsSepClosure ℚ Ω]
    (hloc : ∀ (K : Type) [Field K] [NumberField K]
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
      q.asIdeal.LiesOver (Ideal.span {(2 : ℤ)}) →
      ((q.asIdeal.ramificationIdx ℤ * q.asIdeal.inertiaDeg ℤ : ℕ) : Cardinal) ≤
        Module.rank (PadicInt 2)
          (NK.Reconstruct.Dual
            (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite q))) 2))
    (hker : ∀ (K : Type) [Field K] [NumberField K],
      Module.rank (PadicInt 2) ↥(restrictUnits (K := K)).ker
        ≤ Module.rank (PadicInt 2) (NK.Reconstruct.Dual (IdeleClassGroup K) 2)) :
    ∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N →
      Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (IdeleClassGroup ↥M) 2)
          - NK.Reconstruct.rComplex ↥M
        ≤ Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (IdeleClassGroup ↥N) 2)
          - NK.Reconstruct.rComplex ↥N :=
  ideleDefectMono_of_components Ω
    (fun K _ _ => intDualRank_eq_finrank_of_rank_eq K
      (rank_dual_integralIdeles_eq_finrank K (hloc K)))
    (fun K _ _ => idcDualRank_add_unitsImgRank_of_le K (hker K))
    (fun M N _ _ hMN => unitsImgRank_naturality Ω M N hMN)

/-- **The requested lemma** — the monotonicity of the idèle-side defect (CoNF (10.3.7) Corollary
with (10.3.20) on `C_K`). -/
theorem ideleDefectMono_attempt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω] :
    ∀ (M N : IntermediateField ℚ Ω) [NumberField ↥M] [NumberField ↥N], M ≤ N →
      Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥M) 2)
          - NK.Reconstruct.rComplex ↥M
        ≤ Module.finrank (PadicInt 2)
          (NK.Reconstruct.Dual (NK.GlobalCFT.IdeleClassGroup ↥N) 2)
          - NK.Reconstruct.rComplex ↥N :=
  ideleDefectMono_attempt_of_components Ω
    (fun K _ _ q hq => NK.NUV2.localUnitDualRank_lowerBound K q hq)
    (fun K _ _ => NK.NUV2.rank_ker_restrictUnits_le_rank_dual_classGroup K)


end NK.NUV2
