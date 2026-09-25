import Mathlib
import Submission.Work.Defs.Basic
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Assembly.Main
import Submission.Work.Tower.APDensity.Main
import Submission.Work.Tower.Assembly.exists_tower_intermediateField
import Submission.Work.Tower.CyclotomicBase.Main
import Submission.Work.ClassNumber.Bound
import Submission.Work.Tower.MinkowskiGS.Defs
import Submission.Work.Tower.MinkowskiGS.Endgame
import Submission.Work.Tower.MinkowskiGS.Bridge
import Submission.Work.Tower.MinkowskiGS.Numeric.exists_minkowski_parameters
import Submission.Work.Tower.MinkowskiGS.Minkowski.classGroupTorsion_finrank_le_minkowski

/-!
# The (a)-only assembly: from the class-group relation bound to `Work.Interface.exists_tower`

This file re-architects the final assembly so that the arithmetic input is **Koch's fact (a)**
only.  The three ingredients are

* the cyclotomic base `Work.Tower.exists_cubic_unramified_extension_data` (proved);
* the Chebotarev splitting primes of `Work.Tower.Assembly.exists_primes_split` (proved);
* the Golod–Šafarevič endgame with the **class-group** relation bound
  `Work.Tower.MinkowskiGS.unramified_tower_gs_classGroup`, fed by
  `Work.Tower.MinkowskiGS.ClassGroupRelationBound` and the numerical heart
  `Work.Tower.MinkowskiGS.Numeric.exists_minkowski_parameters`.

The single arithmetic input is `Work.Tower.MinkowskiGS.KochInjectionInput`, fact (a) at the finite
maximal `T`-split level; the wrappers at the end of the file turn fact (a) into the statement of
`Work.Interface.exists_tower`:

* `Work.Tower.MinkowskiGS.exists_tower_of_classGroupRelationBound` — from the bound;
* `Work.Tower.MinkowskiGS.exists_tower_of_kochInjectionInput` — from fact (a);
* `Work.Tower.MinkowskiGS.exists_tower_of_abstractKochInput` — from the abstract form of fact (a)
  plus the (non-arithmetic) cutting data.

No class-group rank formula (b′), i.e. no Artin reciprocity, is used anywhere.
-/

open NumberField
open scoped Classical nonZeroDivisors IsMulCommutative

set_option linter.style.haveILetI false

namespace Work
namespace Tower
namespace MinkowskiGS

open Work.Tower.Assembly (three_not_dvd_prod isPGroup_three_of_exp rootDiscr_eq_exp
  eq_witness_of_mem_splits)

/-- **The final reduction with the bare-type base interface.**  From the class-group relation
bound `ClassGroupRelationBound` (Koch (a) + the proved Kummer/Minkowski computation) and the
cyclotomic base of the tower, one obtains the statement of `Work.Interface.exists_tower`. -/
theorem exists_tower_of_base_classGroup
    (hbase : ∀ (ℓ : ℕ) (_ : 0 < ℓ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) →
      (∀ i, r i % 3 = 1) → Function.Injective r →
      ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyReal F)
        (_ : IsGalois ℚ F)
        (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra F M)
        (_ : FiniteDimensional F M) (_ : IsGalois F M),
        Module.finrank ℚ F = 3 ∧ IsAbelianGalois F M ∧ Module.finrank F M = 3 ^ (ℓ - 1) ∧
        (∀ σ : Gal(M/F), σ ^ 3 = 1) ∧ Work.Tower.IsUnramifiedExtension F M ∧
        |NumberField.discr F| = ((∏ i, r i : ℕ) : ℤ) ^ 2)
    (h : ClassGroupRelationBound) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  intro H hH
  classical
  -- ## 0. the numerical parameters
  obtain ⟨C_M, hCMpos, hCM⟩ := Work.ClassNumber.Bound
  obtain ⟨C_A, hCA, hap⟩ := Work.Tower.exists_primes_mod_three_log_sum
  obtain ⟨ℓ, r, t, C, hr, hrinj, hr3, hℓpos, htpos, hC1, hCdef, hnumC, _htdef, hnum_dimCl⟩ :=
    Work.Tower.MinkowskiGS.Numeric.exists_minkowski_parameters C_A hCA hap C_M hCMpos H hH
  -- ## 1. the base field
  obtain ⟨F, hFF, hFN, hFTR, hFgal, M, hMF, hMN, hFM, hFMD, hFMG,
    hF3, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩ := hbase ℓ hℓpos r hr hr3 hrinj
  letI : Field F := hFF
  letI : NumberField F := hFN
  letI : NumberField.IsTotallyReal F := hFTR
  letI : IsGalois ℚ F := hFgal
  letI : Field M := hMF
  letI : NumberField M := hMN
  letI : Algebra F M := hFM
  letI : FiniteDimensional F M := hFMD
  letI : IsGalois F M := hFMG
  -- ## 2. `3 ∤ disc F`
  have h3disc : ¬ (3 : ℤ) ∣ NumberField.discr F := by
    intro hd
    have h1 : (3 : ℤ) ∣ |NumberField.discr F| :=
      (dvd_abs (3 : ℤ) (NumberField.discr F)).mpr hd
    rw [hFdisc] at h1
    have h2 : (3 : ℤ) ∣ ((∏ i, r i : ℕ) : ℤ) := by
      have hp : Prime (3 : ℤ) := by norm_num
      exact hp.dvd_of_dvd_pow h1
    exact three_not_dvd_prod r hr hr3 (by exact_mod_cast h2)
  -- ## 3. the Frattini layer `E/F`
  obtain ⟨E, hEF, hEN, hEA, hEFin, hEgal, hEunr, hE3, hEab, hEexp, hEuniv⟩ :=
    Work.Tower.exists_frattini_layer F h3disc
  letI : Field E := hEF
  letI : NumberField E := hEN
  letI : Algebra F E := hEA
  letI : FiniteDimensional F E := hEFin
  letI : IsGalois F E := hEgal
  haveI : Fintype (Gal(E/F)) := Fintype.ofFinite _
  -- ## 4. a finite Galois extension of `ℚ` containing `E`
  obtain ⟨N, hNF, hNN, hNA, hNtow, hNgal, hNfin, φ, hNsplit⟩ :=
    Glue.exists_galois_closure_split F E
  letI : Field N := hNF
  letI : NumberField N := hNN
  letI : Algebra F N := hNA
  letI : IsScalarTower ℚ F N := hNtow
  letI : IsGalois ℚ N := hNgal
  letI : FiniteDimensional F N := hNfin
  -- ## 5. the split primes `q b`
  obtain ⟨q, hq, hqi, hq4, hqsplit⟩ := Assembly.exists_primes_split N t
  have hsplitE : ∀ b, Work.Defs.SplitsCompletely (q b) E := fun b =>
    hNsplit (q b) (hq b) (hqsplit b)
  have hsplitF : ∀ b, Work.Defs.SplitsCompletely (q b) F := fun b =>
    ((Work.Tower.splitsCompletely_iff_relative (F := F) (L := E) (q b) (hq b)).mp
      (hsplitE b)).1
  have hsplitEin : ∀ b (𝔭 : Ideal (𝓞 F)), 𝔭.IsPrime → ((q b : ℕ) : 𝓞 F) ∈ 𝔭 →
      Work.Tower.SplitsCompletelyIn F E 𝔭 := fun b =>
    ((Work.Tower.splitsCompletely_iff_relative (F := F) (L := E) (q b) (hq b)).mp
      (hsplitE b)).2
  -- ## 6. the set `T` of primes of `F` above the `q b`
  have hsplitFkeep : ∀ b, Work.Defs.SplitsCompletely (q b) F := hsplitF
  choose 𝔮 h𝔮prime h𝔮mem _h𝔮res _h𝔮ne h𝔮prod using hsplitF
  let T : Finset (Ideal (𝓞 F)) :=
    Finset.univ.image (fun bi : Fin t × Fin (Module.finrank ℚ F) => 𝔮 bi.1 bi.2)
  have hTmem : ∀ {𝔭 : Ideal (𝓞 F)}, 𝔭 ∈ T →
      ∃ (b : Fin t) (i : Fin (Module.finrank ℚ F)), 𝔮 b i = 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨⟨b, i⟩, -, hbi⟩ := Finset.mem_image.mp h𝔭
    exact ⟨b, i, hbi⟩
  have hTprime : ∀ 𝔭 ∈ T, 𝔭.IsPrime := by
    intro 𝔭 h𝔭
    obtain ⟨b, i, rfl⟩ := hTmem h𝔭
    exact h𝔮prime b i
  have hTcard : T.card ≤ 3 * t := by
    calc T.card ≤ (Finset.univ : Finset (Fin t × Fin (Module.finrank ℚ F))).card :=
          Finset.card_image_le
      _ = t * Module.finrank ℚ F := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      _ = 3 * t := by rw [hF3]; ring
  -- ## 7. the Frattini condition for `T`
  have hTsplit : ∀ 𝔭 ∈ T, ∀ (L : Type) [Field L] [NumberField L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      Work.Tower.IsUnramifiedExtension F L → IsAbelianGalois F L →
      (∀ σ : Gal(L/F), σ ^ 3 = 1) → Work.Tower.SplitsCompletelyIn F L 𝔭 := by
    intro 𝔭 h𝔭 L _ _ _ _ _ hLunr hLab hLexp
    obtain ⟨b, i, rfl⟩ := hTmem h𝔭
    haveI : Fintype (Gal(L/F)) := Fintype.ofFinite _
    have hL3 : IsPGroup 3 (Gal(L/F)) := isPGroup_three_of_exp (G := Gal(L/F)) hLexp
    obtain ⟨ψ, -⟩ := hEuniv L hLunr hL3 hLab hLexp
    exact Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom (𝔮 b i) ψ
      (hsplitEin b (𝔮 b i) (h𝔮prime b i) (h𝔮mem b i))
  -- ## 8. the relation-rank bound at the maximal `T`-split level
  set dimCl : ℕ := Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) with hdimCl_def
  have hshafT : ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K]
      [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      (∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
        [IsGalois F L],
        Work.Tower.IsUnramifiedExtension F L → IsPGroup 3 (Gal(L/F)) →
        (∀ 𝔭 ∈ T, Work.Tower.SplitsCompletelyIn F L 𝔭) → ∃ (φ : L →ₐ[F] K), True) →
      Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤ (dimCl + 2) + T.card :=
    fun K _ _ _ _ _ hKur hK3 hmax => h F hF3 K hKur hK3 T hTsplit hmax
  have hm : ℓ - 1 ≤ generatorRank (Gal(M/F)) := Glue.le_generatorRank_galois hFexp hFMdeg
  -- ## 9. the root discriminant of `F`
  have hrdF : NumberField.rootDiscr F = Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) :=
    rootDiscr_eq_exp r (fun i => (hr i).pos) hF3 hFdisc
  -- ## 10. the Minkowski bound on `dim Cl_F[3]`
  have hdimClBound : (dimCl : ℝ) ≤ 3 * Real.logb 3 (C_M *
      Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) *
      (1 + Real.log (Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ))))) := by
    have hB := Work.Tower.MinkowskiGS.Minkowski.classGroupTorsion_finrank_le_minkowski F hF3 C_M hCMpos hCM
    rw [hrdF] at hB
    rw [hdimCl_def]
    exact hB
  -- ## 11. the numerical condition `(ℓ-1)² > 4((dimCl + 2) + |T|)`
  have hnum : (ℓ - 1) ^ 2 > 4 * ((dimCl + 2) + T.card) := by
    have h3 : (((ℓ - 1 : ℕ) : ℝ)) ^ 2 > 4 * ((dimCl : ℝ) + 2 + 3 * (t : ℝ)) :=
      hnum_dimCl dimCl hdimClBound
    have hcard : ((T.card : ℕ) : ℝ) ≤ 3 * (t : ℝ) := by exact_mod_cast hTcard
    have h5 : 4 * ((dimCl + 2) + 3 * t) < (ℓ - 1) ^ 2 := by
      have hcast : ((4 * ((dimCl + 2) + 3 * t) : ℕ) : ℝ) < (((ℓ - 1) ^ 2 : ℕ) : ℝ) := by
        have h4 : ((4 * ((dimCl + 2) + 3 * t) : ℕ) : ℝ) =
            4 * ((dimCl : ℝ) + 2 + 3 * (t : ℝ)) := by push_cast; ring
        have h6 : (((ℓ - 1) ^ 2 : ℕ) : ℝ) = (((ℓ - 1 : ℕ) : ℝ)) ^ 2 := by
          rw [Nat.cast_pow]
        rw [h4, h6]
        exact h3
      exact_mod_cast hcast
    have h6 : 4 * ((dimCl + 2) + T.card) ≤ 4 * ((dimCl + 2) + 3 * t) := by omega
    omega
  -- ## 12. the tower, via the Golod–Šafarevič inequality
  have hM3 : IsPGroup 3 (Gal(M/F)) := isPGroup_three_of_exp (G := Gal(M/F)) hFexp
  obtain htower := Work.Tower.MinkowskiGS.unramified_tower_gs_classGroup F hF3 (ℓ - 1) M hFunr hM3
    hFab hFexp hm T hTprime hTsplit (dimCl + 2) hshafT hnum
  -- ## 13. the class-number loss is covered by `C`
  have hCF : 2 * NumberField.rootDiscr F ≤ C := by
    have h1 : (1 : ℝ) ≤ Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) := by
      rw [← hrdF]
      exact Work.one_le_rootDiscr F
    rw [hCdef, max_eq_right (by linarith : (1 : ℝ) ≤
      2 * Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)))]
    linarith [hrdF.le]
  -- ## 14. conclusion: the CM field `K = L(i)`
  refine ⟨t, q, C, htpos, hq, hqi, hq4, hC1, hnumC, fun N₀ => ?_⟩
  obtain ⟨L, hLF, hLN, hLA, hLfin, hLgal, hLdeg, hLunr, hL3, hLsplit⟩ := htower (2 * N₀)
  letI : Field L := hLF
  letI : NumberField L := hLN
  letI : Algebra F L := hLA
  letI : FiniteDimensional F L := hLfin
  letI : IsGalois F L := hLgal
  haveI : NumberField.IsTotallyReal L :=
    Work.Tower.isTotallyReal_of_isPGroup_three_unramified hFTR hLunr hL3
  have hqL : ∀ b, Work.Defs.SplitsCompletely (q b) L := by
    intro b
    refine (Work.Tower.splitsCompletely_iff_relative (F := F) (L := L) (q b) (hq b)).mpr
      ⟨hsplitFkeep b, ?_⟩
    intro 𝔭 h𝔭 hmem
    obtain ⟨i, hi⟩ := eq_witness_of_mem_splits (q b) (hq b) (𝔮 b) (h𝔮prime b) (h𝔮mem b)
      (h𝔮prod b) 𝔭 h𝔭 hmem
    have hmemT : 𝔮 b i ∈ T :=
      Finset.mem_image.mpr ⟨(b, i), Finset.mem_univ _, rfl⟩
    rw [← hi]
    exact hLsplit (𝔮 b i) hmemT
  obtain ⟨K, hKF, hKN, hKAlg, hKtow, hKCM, _hK2, hKdeg, hKrd, hKsplit⟩ :=
    Work.Tower.exists_cm_adjoin L inferInstance
  letI : Field K := hKF
  letI : NumberField K := hKN
  letI : Algebra L K := hKAlg
  letI : IsScalarTower ℚ L K := hKtow
  letI : NumberField.IsCMField K := hKCM
  have hrdL : NumberField.rootDiscr L = NumberField.rootDiscr F :=
    Work.Tower.rootDiscr_eq_of_isUnramifiedExtension hLunr
  refine ⟨K, hKF, hKN, hKCM, ?_, ?_, ?_⟩
  · rw [hKdeg]; omega
  · rw [hrdL] at hKrd; linarith
  · intro b
    exact hKsplit (q b) (hq b) (hq4 b) (hqL b)


/-- **The final reduction with the `IntermediateField` base interface.**  As
`exists_tower_of_base_classGroup`, but the cyclotomic base is presented as
`Work.Tower.exists_cubic_unramified_extension_data` states it (an intermediate field of a Galois
extension of `ℚ`), and the carrier is converted to a bare type as in
`Work.Tower.AssemblyProP.exists_tower_intermediateField_pos`. -/
theorem exists_tower_intermediateField_classGroup
    (hbase : ∀ (ℓ : ℕ) (_ : 0 < ℓ) (r : Fin ℓ → ℕ), (∀ i, Nat.Prime (r i)) →
      (∀ i, r i % 3 = 1) → Function.Injective r →
      ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ℚ M) (_ : IsGalois ℚ M)
        (F : IntermediateField ℚ M),
        Module.finrank ℚ ↥F = 3 ∧ IsGalois ℚ ↥F ∧ NumberField.IsTotallyReal ↥F ∧
        IsAbelianGalois ↥F M ∧ Module.finrank ↥F M = 3 ^ (ℓ - 1) ∧
        (∀ σ : Gal(M/↥F), σ ^ 3 = 1) ∧ Work.Tower.IsUnramifiedExtension ↥F M ∧
        |NumberField.discr ↥F| = ((∏ i, r i : ℕ) : ℤ) ^ 2)
    (h : ClassGroupRelationBound) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  refine Work.Tower.MinkowskiGS.exists_tower_of_base_classGroup ?_ h
  intro ℓ hℓ r hr hr3 hrinj
  obtain ⟨M, hMF, hMN, hMA, hMG, F, hF3, hFgal, hFTR, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩ :=
    hbase ℓ hℓ r hr hr3 hrinj
  letI : Field M := hMF
  letI : NumberField M := hMN
  letI : Algebra ℚ M := hMA
  letI : IsGalois ℚ M := hMG
  refine ⟨↥F, inferInstance, inferInstance, hFTR, hFgal, M, inferInstance, inferInstance,
    inferInstance, ?_, hFab.toIsGalois, ?_, hFab, hFMdeg, hFexp, hFunr, hFdisc⟩
  · exact Module.finite_of_finrank_pos (by rw [hFMdeg]; positivity)
  · refine Eq.trans ?_ hF3
    refine Work.Tower.Assembly.finrank_congr_of_smul _ _ _ _ ?_
    intro q a
    apply Subtype.ext
    rw [Algebra.smul_def]
    simp only [IntermediateField.coe_mul]
    rw [Work.Tower.Assembly.coe_algebraMap_eq F _ q, IntermediateField.coe_smul, Algebra.smul_def]

/-- **The final assembly, from the class-group relation bound.**

The cyclotomic base is supplied by the *proved* `Work.Tower.exists_cubic_unramified_extension_data`
(paper Proposition 3.2); the arithmetic input is only `ClassGroupRelationBound`, which by
`Work.Tower.MinkowskiGS.classGroupRelationBound_of_kochInjectionInput` is a consequence of Koch's
fact (a) alone. -/
theorem exists_tower_of_classGroupRelationBound (h : ClassGroupRelationBound) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  refine Work.Tower.MinkowskiGS.exists_tower_intermediateField_classGroup ?_ h
  intro ℓ hℓ r hr hr3 hrinj
  obtain ⟨M, hMF, hMN, hMA, hMG, F, h1, h2, h3, h4, _h5, h6, h7, h8, h9⟩ :=
    Work.Tower.exists_cubic_unramified_extension_data ℓ hℓ r hr hr3 hrinj
  exact ⟨M, hMF, hMN, hMA, hMG, F, h1, h2, h3, h6, h4, h7, h8, h9⟩

/-- **The deliverable, in the form to be imported: Koch's fact (a) alone implies
`Work.Interface.exists_tower`.**

The hypothesis `KochInjectionInput` is fact (a) for every totally real cubic field `F`, at the
finite maximal `T`-split level; no class-group rank formula (b′) and hence no Artin reciprocity is
used. -/
theorem exists_tower_of_kochInjectionInput (h : KochInjectionInput) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) :=
  Work.Tower.MinkowskiGS.exists_tower_of_classGroupRelationBound
    (Work.Tower.MinkowskiGS.classGroupRelationBound_of_kochInjectionInput h)

/-- **The deliverable in the abstract-group form**: the `∃ G` statement of fact (a) for every
totally real cubic field, together with the group-theoretic cutting data, implies
`Work.Interface.exists_tower`. -/
theorem exists_tower_of_abstractKochInput (h : AbstractKochInput) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) :=
  Work.Tower.MinkowskiGS.exists_tower_of_classGroupRelationBound
    (Work.Tower.MinkowskiGS.classGroupRelationBound_of_abstractKochInput h)


/-- **The deliverable in the requester's literal phrasing.**

`hkoch` is *verbatim* the statement "Koch's fact (a) for every totally real cubic field `F`", in the
`∃ G` form: for each such `F` there is an abstract group `G` modelling its maximal
everywhere-unramified pro-`3` group with `ShafarevichInjection F 3 G`.  `hcut` is the
**non-arithmetic** group-theoretic cutting (`KochTransfer` and `SplittingCut` for that `G`), which
is what passes from the abstract maximal group to its finite `T`-split quotients; it involves no
class-group rank formula.  Together they give the statement of `Work.Interface.exists_tower`. -/
theorem exists_tower_of_kochInjection_of_cutting
    (hkoch : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
      Module.finrank ℚ F = 3 →
      ∃ (G : Type) (_ : Group G), Work.CFT.ShafarevichCore.ShafarevichInjection F 3 G)
    (hcut : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
      (_ : Module.finrank ℚ F = 3) (G : Type) [Group G],
      Work.CFT.ShafarevichCore.ShafarevichInjection F 3 G →
      Work.CFT.Kummer.KochTransfer 3 G ∧ Work.CFT.ShafarevichCore.SplittingCut F G) :
    ∀ (H : ℝ), 0 < H →
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧
      Function.Injective q ∧ (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧
      (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  refine Work.Tower.MinkowskiGS.exists_tower_of_abstractKochInput ?_
  intro F _ _ _ hdeg
  obtain ⟨G, hG, hinj⟩ := hkoch F hdeg
  obtain ⟨hk, hc⟩ := hcut F hdeg G hinj
  exact ⟨G, hG, hk, hinj, hc⟩


end MinkowskiGS
end Tower
end Work
