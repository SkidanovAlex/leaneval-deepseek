import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.S4ExpF.Bridge
import Submission.Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos
import Submission.Work.WilC5.LogTranslation
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.StepSeqUnbounded
import Submission.Work.WilC5.expE_strictMono

set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-!
  WilC5 — the definable logarithm of a *unit* of the standard real valuation is finite.

  The standard real valuation of an ordered field `K` (vdDMM (1.1)) has for value the archimedean
  class; its *units* are the elements in the archimedean class of `1`,
  `IsUnitVal y := ∃ N, ((N:K)+1)⁻¹ ≤ |y| ∧ |y| ≤ (N:K)+1`.  The claim is that the definable
  logarithm (`logFun`, the graph of which is `logDefSet`) maps units into the valuation ring
  `Fin(K) = IsFiniteVal`:

      `IsUnitVal y → IsFiniteVal (logFun y)`.

  The mathematical content is just that `1/k ≤ y ≤ k` and `exp` increasing imply
  `-log k ≤ log y ≤ log k`, and `log k ≤ k` for a natural number `k ≥ 1` (because
  `exp 1 ≥ 2`, so `exp k ≥ 2^k ≥ k`).

  Formally we use that `K ⊨ TE = Th(ℝ, exp)`, so `LEc`-sentences true in `ℝ` transfer to `K`
  (`Work.WilC5.transfer`): `exp` is strictly increasing (`Work.WilC5.expE_strictMono`) and
  `2 ≤ exp 1` (below).  For `0 < y`, `exp (log y) = y` (`Work.WilC5.expE_logFun_of_pos`), and for
  `y ≤ 0` the logarithm vanishes (`Work.WilC5.S4ExpF.logFun_eq_zero_of_not_pos`).
-/

/-! ## 1. `2 ≤ exp 1` in every model of `TE` -/

/-- The `LEc`-sentence `1 + 1 ≤ exp 1`. -/
def expOneGeTwoForm : LEc.BoundedFormula Empty 0 :=
  leForm (eAdd (eOne : LEc.Term (Empty ⊕ Fin 0)) eOne)
    (eExp (eOne : LEc.Term (Empty ⊕ Fin 0)))

theorem expOneGeTwoForm_realize {M : Type} [LEc.Structure M] (xs : Fin 0 → M) :
    expOneGeTwoForm.Realize (emptyVar : Empty → M) xs ↔
      leE (M := M) (addE (oneE : M) oneE) (expE (oneE : M)) := by
  rw [expOneGeTwoForm, leForm_realize, realize_eAdd, realize_eExp, realize_eOne]
  rfl

theorem expOneGeTwoForm_real (xs : Fin 0 → ℝ) :
    expOneGeTwoForm.Realize (emptyVar : Empty → ℝ) xs := by
  rw [expOneGeTwoForm_realize, leE_real, addE_real, oneE_real, expE_real]
  linarith [Real.exp_one_gt_two]

/-- **`2 ≤ exp 1` in every model of `TE`** (the transfer of `2 < e`). -/
theorem expE_one_ge_two {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] (hM : K ⊨ TE)
    (hadd : ∀ x y : K, addE x y = x + y) (hone : (oneE : K) = 1)
    (hleneg : ∀ x y : K, leE x y ↔ x ≤ y) :
    (2 : K) ≤ expE (1 : K) := by
  have h := transfer hM expOneGeTwoForm expOneGeTwoForm_real Fin.elim0
  rw [expOneGeTwoForm_realize, hadd, hone, hleneg] at h
  linarith

/-! ## 2. `exp` of a standard natural dominates that natural -/

/-- **`2 ^ n ≤ exp n` in every model of `TE`.**  By induction: `exp 0 = 1` and
`exp (n+1) = exp n · exp 1 ≥ 2^n · 2 = 2^{n+1}`. -/
theorem expE_ge_two_pow {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] (hM : K ⊨ TE)
    (hadd : ∀ x y : K, addE x y = x + y) (hmul : ∀ x y : K, mulE x y = x * y)
    (hone : (oneE : K) = 1) (hleneg : ∀ x y : K, leE x y ↔ x ≤ y) :
    ∀ n : ℕ, (2 : K) ^ n ≤ expE ((n : ℕ) : K) := by
  have h2 : (2 : K) ≤ expE (1 : K) := expE_one_ge_two hM hadd hone hleneg
  intro n
  induction n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero]
      rw [← S4ExpF.zeroE_eq_zero hM hadd, expE_zero_of_model hM, hone]
  | succ n ih =>
      have hstep : expE (((n + 1 : ℕ) : K)) = expE ((n : ℕ) : K) * expE (1 : K) := by
        rw [Nat.cast_succ, ← hadd ((n : ℕ) : K) 1, expE_add_of_model hM, hmul]
      rw [hstep, pow_succ]
      have hexpn : (0 : K) ≤ expE ((n : ℕ) : K) := le_trans (by positivity) ih
      exact mul_le_mul ih h2 (by norm_num) hexpn

/-- **`n ≤ exp n` for a standard natural `n`, in every model of `TE`.**  Indeed
`n ≤ 2^n ≤ exp n`. -/
theorem expE_nat_ge {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K] (hM : K ⊨ TE)
    (hadd : ∀ x y : K, addE x y = x + y) (hmul : ∀ x y : K, mulE x y = x * y)
    (hone : (oneE : K) = 1) (hleneg : ∀ x y : K, leE x y ↔ x ≤ y) (n : ℕ) :
    ((n : ℕ) : K) ≤ expE ((n : ℕ) : K) := by
  have hpow := expE_ge_two_pow hM hadd hmul hone hleneg n
  have hle : n ≤ (2 : ℕ) ^ n := le_of_lt (Nat.lt_two_pow_self (n := n))
  have hcast : ((n : ℕ) : K) ≤ (((2 : ℕ) ^ n : ℕ) : K) := Nat.cast_le.mpr hle
  have hcast2 : (((2 : ℕ) ^ n : ℕ) : K) = (2 : K) ^ n := by
    rw [Nat.cast_pow]; norm_num
  rw [hcast2] at hcast
  exact le_trans hcast hpow

/-! ## 3. The main statement -/

theorem LogUnitFinite
    {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE]
    (hrexp : ∀ x : K, @FirstOrder.Language.Structure.funMap WilkiesDesign.CG.rexpL K _ 1
        WilkiesDesign.CG.rexpFunc.rexp ![x] = Work.WilC5.rexpFromExp x)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {y : K} (hy : WilkiesDesign.CG.IsUnitVal y) :
    Work.WilC5.IsFiniteVal (Work.WilC5.logFun y) := by
  have hM : K ⊨ TE := inferInstance
  obtain ⟨N, hlow, hhigh⟩ := hy
  rcases lt_or_ge (0 : K) y with hypos | hynonpos
  · -- `0 < y`: `-A ≤ log y ≤ A` for `A = (N : K) + 1`
    set A : K := (N : K) + 1 with hAdef
    have hApos : 0 < A := by rw [hAdef]; positivity
    have hyabs : |y| = y := abs_of_pos hypos
    have hlow' : A⁻¹ ≤ y := by rw [hAdef]; rwa [hyabs] at hlow
    have hhigh' : y ≤ A := by rw [hAdef]; rwa [hyabs] at hhigh
    -- `exp` inverts `log` at `y`
    have hlog : expE (logFun y) = y :=
      expE_logFun_of_pos (M := K) hM ((S4ExpF.leE_zero_iff hM hadd hleneg y).mpr hypos)
    -- `A ≤ exp A`
    have hAge : A ≤ expE A := by
      have hnat := expE_nat_ge hM hadd hmul hone hleneg (N + 1)
      have hc : ((N + 1 : ℕ) : K) = (N : K) + 1 := Nat.cast_succ N
      rw [hAdef, ← hc]
      exact hnat
    have hexpApos : 0 < expE A := lt_of_lt_of_le hApos hAge
    -- upper bound
    have hle_upper : logFun y ≤ A := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : leE A (logFun y) := (hleneg A _).mpr (le_of_lt hcon)
      have h2 : ¬ leE (logFun y) A := fun hh => (not_le.mpr hcon) ((hleneg _ A).mp hh)
      have hmono := expE_strictMono (M := K) hM ⟨h1, h2⟩
      rw [hlog] at hmono
      exact hmono.2 ((hleneg y (expE A)).mpr (le_trans hhigh' hAge))
    -- lower bound
    have hle_lower : -A ≤ logFun y := by
      have hmul1 : expE (-A) * expE A = 1 := by
        have h := expE_add_of_model (M := K) hM (-A) A
        rw [hadd, neg_add_cancel, hmul] at h
        rw [← h, ← S4ExpF.zeroE_eq_zero hM hadd, expE_zero_of_model hM, hone]
      have hexpneg : expE (-A) = (expE A)⁻¹ := eq_inv_of_mul_eq_one_left hmul1
      have hle1 : (expE A)⁻¹ ≤ A⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hApos hAge
      have hexpneg_le : expE (-A) ≤ y := by
        rw [hexpneg]
        exact le_trans hle1 hlow'
      by_contra hcon
      rw [not_le] at hcon
      have h1 : leE (logFun y) (-A) := (hleneg _ _).mpr (le_of_lt hcon)
      have h2 : ¬ leE (-A) (logFun y) := fun hh => (not_le.mpr hcon) ((hleneg _ _).mp hh)
      have hmono := expE_strictMono (M := K) hM ⟨h1, h2⟩
      rw [hlog] at hmono
      exact hmono.2 ((hleneg _ y).mpr hexpneg_le)
    refine ⟨N, ?_⟩
    rw [hAdef] at hle_lower hle_upper
    exact abs_le.mpr ⟨hle_lower, hle_upper⟩
  · -- `y ≤ 0`: the definable logarithm vanishes
    have hz : logFun y = 0 :=
      S4ExpF.logFun_eq_zero_of_not_pos hM hadd hone hleneg y (not_lt.mpr hynonpos)
    refine ⟨0, ?_⟩
    rw [hz]
    norm_num

end Work.WilC5
