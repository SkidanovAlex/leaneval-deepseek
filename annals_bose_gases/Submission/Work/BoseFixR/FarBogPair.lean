import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.pairOp_shift_identity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `FarBogPair` — FS `thm:BogHamDiag`'s zero-point bound in the `BoseBoxFock` vocabulary

This is the requester's lemma: verbatim `Work.BoseBogFS.qw_KzBogFS_ge` (FS `thm:BogHamDiag`'s
zero-point bound for the quadratic Bogoliubov Hamiltonian `𝒦^Bog = KzBogFS`), restated in the
`Work.BoseBoxFock` / `Work.BoseFixR` vocabulary.  The module `Submission.Work.BoseBogFS.Defs`
is unimportable from here (it redefines `Work.BoseFixR.KzDatum.viewFS`), so the proof is
*ported* rather than imported:

* `Work.BoseFixR.zpA/zpB/zpC` are FS's `𝒜(k)`, `ℬ(k)`, `𝒞(k)` read off
  `Work.BoseFixR.KzEnvAt E ρ` and `Work.BoseFixR.cCoefFar`;
* `pairOpFar_eq_zp` / `KzBogFS_eq_sum_pairOpFar` rewrite `KzBogFS` as the half-weighted sum of
  the per-pair quadratics `Work.BoseFixR.pairOpFar`;
* `zpPairOp_eq_shifted` is the generic per-pair Bogoliubov identity
  `Work.BoseFixR.pairOp_shift_identity` (FS `eq:BogIdentity` at FS's `b_k` of `eq:Defb_k`,
  proved in `Submission/Work/BoseFixR/pairOp_shift_identity.lean`), specialised;
* `zpPairOp_ground` is the per-pair ground estimate (FS `eq:BogIneq`) — verbatim
  `Work.BoseBogFS.bogPairOp_ground`;
* `qw_sum_finset_zp`/`qw_sum_smul_zp` are the finite-sum linearity of the Fock form —
  verbatim `Work.BoseBogFS.qw_sum_finset`;
* the assembly is `Work.BoseBogFS.qw_KzBogFS_ge` verbatim.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR

open Work.BoseB7 Work.BoseBoxFock Work.BoseB6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The far-leg vocabulary: FS's pair quadratic read off `KzEnvAt` -/

/-- FS's `𝒜(k) = τ(k) + ρŴ₁(k)` at the datum `(E, ρ)` — the `A`-field of `KzEnvAt E ρ`. -/
noncomputable def zpA (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : ℝ := (KzEnvAt E ρ).A k

/-- FS's `ℬ(k) = ρŴ₁(k)` at the datum `(E, ρ)` — the `B`-field of `KzEnvAt E ρ`. -/
noncomputable def zpB (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : ℝ := (KzEnvAt E ρ).B k

/-- FS's `𝒞(k) = (ρ−μ)Ŵ₁(0)χ̂(kℓ)z` at the datum `(E, ρ)` (the `c`-number coefficient). -/
noncomputable def zpC (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : ℝ := cCoefFar E ρ k

/-- `z = √(ρℓ³)`, FS's substituted condensate amplitude at density `ρ`. -/
noncomputable def zpZ (E : Q3Env Mode) (ρ : ℝ) : ℝ := (KzEnvAt E ρ).z

/-- FS `eq:Defb_k`'s squeezing parameter `α_k = ℬ_k/(𝒜_k+√(𝒜_k²−ℬ_k²))`. -/
noncomputable def zpAlpha (E : Q3Env Mode) (ρ : ℝ) : Mode → ℝ :=
  fun k => Submission.BoseGases.bogAlpha (zpA E ρ k) (zpB E ρ k)

/-- FS `thm:BogHamDiag`'s `𝒟_k = ½(𝒜_k + √(𝒜_k²−ℬ_k²))`. -/
noncomputable def zpD (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.bogD (zpA E ρ k) (zpB E ρ k)

/-- FS `eq:Defb_k`'s `c`-number shift `c_k = 2𝒞_k/(𝒜_k+ℬ_k+√(𝒜_k²−ℬ_k²))`. -/
noncomputable def zpGamma (E : Q3Env Mode) (ρ : ℝ) (k : Mode) : ℝ :=
  Submission.BoseGases.fmsGamma (zpA E ρ k) (zpB E ρ k) (zpC E ρ k)

/-- FS `eq:Defb_k`'s shifted squeezing operator `b_k = a_k + α_ka_{-k}† + c_k`. -/
noncomputable def zpShift (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.bOp (zpAlpha E ρ) k + (zpGamma E ρ k) • (1 : F.H →ₗ[ℝ] F.H)

/-- Its formal adjoint `b_k†` for the Fock form `bp` (the shift is real). -/
noncomputable def zpShiftDag (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  F.bOpDag (zpAlpha E ρ) k + (zpGamma E ρ k) • (1 : F.H →ₗ[ℝ] F.H)

/-- The pair operator of `KzBogFS` in the `zp*` vocabulary: `pairOpFar` unfolded. -/
lemma pairOpFar_eq_zp (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    pairOpFar F E ρ k
      = (zpA E ρ k) • (F.nOp k + F.nOp (-k))
        + (zpB E ρ k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
        + (zpC E ρ k) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)) := rfl

/-- **The definitional identity of the requester's note**: `KzBogFS` is the half-weighted sum
of the per-pair quadratics `pairOpFar`. -/
lemma KzBogFS_eq_sum_pairOpFar (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) :
    KzBogFS F E ρ = ∑ k : Mode, (1 / 2 : ℝ) • pairOpFar F E ρ k := by
  simp only [KzBogFS, pairOpFar, KzEnvAt]

/-- The `zpSumOf` of the `zp*` vocabulary. -/
lemma zpSumOf_eq_zp (E : Q3Env Mode) (ρ : ℝ) :
    zpSumOf E ρ
      = ∑ k : Mode, (1 / 2 : ℝ) * (bogZeroPoint (zpA E ρ k) (zpB E ρ k)
          + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k)) := by
  rw [zpSumOf]
  exact Finset.sum_congr rfl fun k _ => by rw [zpA, zpB, zpC]

/-! ## 2. The per-pair pieces (FS `eq:BogIdentity` / `eq:BogIneq`) -/

/-- The shifted squeezing operator is the adjoint of its dagger for the Fock form. -/
lemma zpShiftDag_bp (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (g f : F.H) :
    F.bp ((zpShiftDag F E ρ k) g) f = F.bp g ((zpShift F E ρ k) f) := by
  simp only [zpShiftDag, zpShift, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, Module.End.one_apply]
  rw [Work.BoseB7.bOpDag_bp F (zpAlpha E ρ) k g f]

/-- The shifted diagonal at a state: `⟨b̂_k x, x⟩ = ‖b̂_k x‖²`. -/
lemma bp_zpShiftDag_zpShift (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (x : F.H) :
    F.bp ((zpShiftDag F E ρ k) ((zpShift F E ρ k) x)) x
      = F.normSq ((zpShift F E ρ k) x) := by
  rw [zpShiftDag_bp F E ρ k ((zpShift F E ρ k) x) x, FockData.normSq]

/-- `2𝒟α² = 𝒜 − √(𝒜²−ℬ²)`: the zero point of the pair is `2𝒟α²`. -/
theorem two_zpD_mul_zpAlpha_sq (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < zpA E ρ k) (hB : |zpB E ρ k| ≤ zpA E ρ k) :
    2 * (zpD E ρ k * (zpAlpha E ρ k) ^ 2)
      = bogZeroPoint (zpA E ρ k) (zpB E ρ k) := by
  have h1 : zpD E ρ k * (zpAlpha E ρ k) ^ 2
      = zpAlpha E ρ k * (zpB E ρ k / 2) := by
    have h := Submission.BoseGases.bog_alpha_mul_D (A := zpA E ρ k) (B := zpB E ρ k) hA hB
    simp only [zpD, zpAlpha] at h ⊢
    linear_combination (Submission.BoseGases.bogAlpha (zpA E ρ k) (zpB E ρ k)) * h
  rw [h1, bogZeroPoint_eq, Submission.BoseGases.bog_A_sub_s_eq hA hB]
  simp only [zpAlpha, zpA, zpB, Submission.BoseGases.bogAlpha]
  field_simp

/-- **FS `eq:BogIdentity` at the `KzEnvAt` datum** — the generic per-pair identity
`Work.BoseFixR.pairOp_shift_identity` specialised to `𝒜 = zpA`, `ℬ = zpB`, `𝒞 = zpC`. -/
lemma zpPairOp_eq_shifted (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < zpA E ρ k) (hB : |zpB E ρ k| ≤ zpA E ρ k) (hAB : 0 < zpA E ρ k + zpB E ρ k)
    (hAe : zpA E ρ (-k) = zpA E ρ k) (hBe : zpB E ρ (-k) = zpB E ρ k)
    (hCe : zpC E ρ (-k) = zpC E ρ k) :
    pairOpFar F E ρ k
      = (zpD E ρ k) • ((zpShiftDag F E ρ k) ∘ₗ (zpShift F E ρ k)
            + (zpShiftDag F E ρ (-k)) ∘ₗ (zpShift F E ρ (-k)))
        - ((zpD E ρ k * (zpAlpha E ρ k) ^ 2 * (F.ccrK k k + F.ccrK (-k) (-k))
            + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k)) • (1 : F.H →ₗ[ℝ] F.H)) := by
  rw [pairOpFar_eq_zp]
  exact pairOp_shift_identity F (zpA E ρ) (zpB E ρ) (zpC E ρ) k hA hB hAB hAe hBe hCe

/-- The value of `pairOpFar` at a state, in the diagonalised form. -/
lemma qw_pairOpFar_eq (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hAε : 0 < zpA E ρ k) (hBε : |zpB E ρ k| ≤ zpA E ρ k)
    (hABε : 0 < zpA E ρ k + zpB E ρ k)
    (hAeε : zpA E ρ (-k) = zpA E ρ k) (hBeε : zpB E ρ (-k) = zpB E ρ k)
    (hCeε : zpC E ρ (-k) = zpC E ρ k) (f : F.H) :
    F.qw f (pairOpFar F E ρ k)
      = (zpD E ρ k) * (F.normSq ((zpShift F E ρ k) f) + F.normSq ((zpShift F E ρ (-k)) f))
        - ((zpD E ρ k * (zpAlpha E ρ k) ^ 2 * (F.ccrK k k + F.ccrK (-k) (-k))
            + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k)) * F.normSq f) := by
  rw [zpPairOp_eq_shifted F E ρ k hAε hBε hABε hAeε hBeε hCeε]
  simp only [FockData.qw, FockData.normSq, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply,
    smul_eq_mul]
  rw [bp_zpShiftDag_zpShift F E ρ k f, bp_zpShiftDag_zpShift F E ρ (-k) f]
  simp only [FockData.normSq]

/-- **FS `eq:BogIneq` per pair**, at FS's coefficients: the pair quadratic is bounded below
by minus the zero point minus the `κ`-error, provided the two commutators sum to at most `2`.
(Verbatim `Work.BoseBogFS.bogPairOp_ground`.) -/
theorem zpPairOp_ground (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hAε : 0 < zpA E ρ k) (hBε : |zpB E ρ k| ≤ zpA E ρ k)
    (hABε : 0 < zpA E ρ k + zpB E ρ k)
    (hAeε : zpA E ρ (-k) = zpA E ρ k) (hBeε : zpB E ρ (-k) = zpB E ρ k)
    (hCeε : zpC E ρ (-k) = zpC E ρ k)
    (hccr : F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) (f : F.H) :
    -((bogZeroPoint (zpA E ρ k) (zpB E ρ k))
        + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k)) * F.normSq f
      ≤ F.qw f (pairOpFar F E ρ k) := by
  rw [qw_pairOpFar_eq F E ρ k hAε hBε hABε hAeε hBeε hCeε f]
  have hDnn : 0 ≤ zpD E ρ k := by
    simp only [zpD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := zpA E ρ k) (B := zpB E ρ k) hAε hBε)
  have hα2 : 0 ≤ zpD E ρ k * (zpAlpha E ρ k) ^ 2 := mul_nonneg hDnn (sq_nonneg _)
  have hzp : 2 * (zpD E ρ k * (zpAlpha E ρ k) ^ 2)
      = bogZeroPoint (zpA E ρ k) (zpB E ρ k) := two_zpD_mul_zpAlpha_sq E ρ k hAε hBε
  have hkey : zpD E ρ k * (zpAlpha E ρ k) ^ 2 * (F.ccrK k k + F.ccrK (-k) (-k))
      ≤ bogZeroPoint (zpA E ρ k) (zpB E ρ k) := by
    have h := mul_le_mul_of_nonneg_left hccr hα2
    linarith [hzp]
  have h1 : 0 ≤ F.normSq ((zpShift F E ρ k) f) := F.bp_nonneg _
  have h2 : 0 ≤ F.normSq ((zpShift F E ρ (-k)) f) := F.bp_nonneg _
  have h3 : 0 ≤ F.normSq f := F.bp_nonneg f
  nlinarith [hDnn, h1, h2, h3, hkey]

/-! ## 3. The finite-sum linearity of the Fock form (verbatim `Work.BoseBogFS.Sum`) -/

/-- Applying a finite weighted sum of linear maps to a vector. -/
theorem sum_smul_apply_zp (F : FockData Mode) (s : Finset Mode) (c : Mode → ℝ)
    (T : Mode → F.H →ₗ[ℝ] F.H) (f : F.H) :
    (∑ k ∈ s, c k • T k) f = ∑ k ∈ s, c k • (T k f) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, ih,
        LinearMap.smul_apply]

/-- The Fock form is additive in its first argument over a finite sum. -/
theorem bp_sum_zp (F : FockData Mode) (s : Finset Mode) (y : Mode → F.H) (f : F.H) :
    F.bp (∑ x ∈ s, y x) f = ∑ x ∈ s, F.bp (y x) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, map_add, LinearMap.add_apply, ih]

/-- The quadratic form of a finite weighted sum over a Finset. -/
theorem qw_sum_finset_zp (F : FockData Mode) (s : Finset Mode) (c : Mode → ℝ)
    (T : Mode → F.H →ₗ[ℝ] F.H) (f : F.H) :
    F.qw f (∑ k ∈ s, c k • T k) = ∑ k ∈ s, c k * F.qw f (T k) := by
  rw [FockData.qw, sum_smul_apply_zp F s c T f, bp_sum_zp F s (fun k => c k • (T k f)) f]
  exact Finset.sum_congr rfl fun k _ => by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, FockData.qw]

/-- The quadratic form of a finite constant-weighted sum. -/
theorem qw_sum_smul_zp (F : FockData Mode) (c : ℝ) (T : Mode → F.H →ₗ[ℝ] F.H) (f : F.H) :
    F.qw f (∑ k : Mode, c • T k) = ∑ k : Mode, c * F.qw f (T k) := by
  rw [qw_sum_finset_zp F Finset.univ (fun _ => c) T f]

/-! ## 4. FS `thm:BogHamDiag`'s zero-point bound (the requested lemma) -/

-- NOTE (requester): this is FS `thm:BogHamDiag`'s zero-point bound, i.e. verbatim
-- `Work.BoseBogFS.qw_KzBogFS_ge`, but stated in the `Work.BoseBoxFock` vocabulary.
-- The module `Submission.Work.BoseBogFS.Defs` CANNOT be imported here: it redefines
-- `Work.BoseFixR.KzDatum.viewFS`, which `Submission.Work.BoseBoxFock.Defs` (already in the
-- import cone via `Submission.Work.BoseFixR.RB5FSFixAux`) also defines, so Lean reports
-- "environment already contains ..." (this is exactly why `RB5FSResidV2.lean` does not
-- build). The proofs of `Submission/Work/BoseBogFS/{Pair,PairIdentity,Ground,Sum}.lean` may
-- be read and ported verbatim (with `bogA/bogB/bogC/bogZ/bogAlpha/bogD/bogCcr2` replaced by
-- `(Work.BoseFixR.KzEnvAt E ρ).A/.B/.z`, `Work.BoseFixR.cCoefFar`, and
-- `Work.BoseB6.bogZeroPoint/bogKappaErr`), as may
-- `Submission/Fock2ModeShift.lean`'s `fms_ground_estimate`.
-- The definitional identity `Work.BoseBoxFock.KzBogFS F E ρ
--   = ∑ k, (1/2) • Work.BoseFixR.pairOpFar F E ρ k` holds by
-- `simp only [Work.BoseBoxFock.KzBogFS, Work.BoseFixR.pairOpFar, Work.BoseFixR.KzEnvAt]`.
theorem FarBogPair {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) (f : F.H)
    (hA : ∀ k, 0 < (Work.BoseFixR.KzEnvAt E ρ).A k)
    (hB : ∀ k, |(Work.BoseFixR.KzEnvAt E ρ).B k| ≤ (Work.BoseFixR.KzEnvAt E ρ).A k)
    (hAB : ∀ k, 0 < (Work.BoseFixR.KzEnvAt E ρ).A k + (Work.BoseFixR.KzEnvAt E ρ).B k)
    (hAe : ∀ k, (Work.BoseFixR.KzEnvAt E ρ).A (-k) = (Work.BoseFixR.KzEnvAt E ρ).A k)
    (hBe : ∀ k, (Work.BoseFixR.KzEnvAt E ρ).B (-k) = (Work.BoseFixR.KzEnvAt E ρ).B k)
    (hCe : ∀ k, Work.BoseFixR.cCoefFar E ρ (-k) = Work.BoseFixR.cCoefFar E ρ k)
    (hccr : ∀ k, F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) :
    -(Work.BoseFixR.zpSumOf E ρ) * F.normSq f
      ≤ F.qw f (Work.BoseBoxFock.KzBogFS F E ρ) := by
  have hsum : F.qw f (∑ k : Mode, (1 / 2 : ℝ) • pairOpFar F E ρ k)
      = ∑ k : Mode, (1 / 2 : ℝ) * F.qw f (pairOpFar F E ρ k) :=
    qw_sum_smul_zp F (1 / 2) (fun k => pairOpFar F E ρ k) f
  rw [KzBogFS_eq_sum_pairOpFar, hsum]
  have hper : ∀ k : Mode,
      -((bogZeroPoint (zpA E ρ k) (zpB E ρ k))
          + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k)) * F.normSq f
        ≤ F.qw f (pairOpFar F E ρ k) := fun k =>
    zpPairOp_ground F E ρ k (hA k) (hB k) (hAB k) (hAe k) (hBe k) (hCe k) (hccr k) f
  have h1 : (∑ k : Mode,
        (1 / 2 : ℝ) * ((-(bogZeroPoint (zpA E ρ k) (zpB E ρ k)
          + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k))) * F.normSq f))
      ≤ (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (pairOpFar F E ρ k)) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hper k) (by norm_num)
  have h2 : (∑ k : Mode,
        (1 / 2 : ℝ) * ((-(bogZeroPoint (zpA E ρ k) (zpB E ρ k)
          + bogKappaErr (zpA E ρ k) (zpB E ρ k) (zpC E ρ k))) * F.normSq f))
      = -(zpSumOf E ρ) * F.normSq f := by
    rw [zpSumOf_eq_zp, neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h2] at h1
  exact h1

end Work.BoseFixR
